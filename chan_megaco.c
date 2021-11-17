#include "asterisk.h"


ASTERISK_FILE_VERSION(__FILE__, "$Revision: 400050 $")

#include <sys/socket.h>
#include <sys/ioctl.h>
#include <net/if.h>
#include <fcntl.h>
#include <netdb.h>
#include <sys/signal.h>
#include <signal.h>
#include <netinet/in.h>
#include <netinet/in_systm.h>
#include <netinet/ip.h>
#include <arpa/inet.h>
#include <ctype.h>

#include "asterisk/lock.h"
#include "asterisk/channel.h"
#include "asterisk/config.h"
#include "asterisk/module.h"
#include "asterisk/pbx.h"
#include "asterisk/sched.h"
#include "asterisk/io.h"
#include "asterisk/rtp_engine.h"
#include "asterisk/acl.h"
#include "asterisk/callerid.h"
#include "asterisk/cli.h"
#include "asterisk/say.h"
#include "asterisk/cdr.h"
#include "asterisk/astdb.h"
#include "asterisk/features.h"
#include "asterisk/app.h"
#include "asterisk/musiconhold.h"
#include "asterisk/utils.h"
#include "asterisk/netsock2.h"
#include "asterisk/causes.h"
#include "asterisk/dsp.h"
#include "asterisk/devicestate.h"
#include "asterisk/stringfields.h"
#include "asterisk/abstract_jb.h"
#include "asterisk/event.h"
#include "asterisk/chanvars.h"
#include "asterisk/pktccops.h"
#include "sip/include/sip.h"

//megaco  digit map definition
// *  -> E
// #  -> F
// S  -> short timer
// L -> Long timer 
//.  -> any digit 
//  "[0-9EF] .L" said the dial with the numbers 0 to 9,and the letter "*", "#" at the beginning of any position as long as the timer after a timeout will be reported.
/*
 * Define to work around buggy dlink MGCP phone firmware which
 * appears not to know that "rt" is part of the "G" package.
 */
/* #define DLINK_BUGGY_FIRMWARE	*/

#define MGCPDUMPER
//#define DEFAULT_EXPIRY	120
#define MAX_EXPIRY	3600
#define DIRECTMEDIA	1
#define NEW_DIGIT_ANALYZE
#define	NEW_FIND_SUBCHANNLE

#define ALLOW_DIRECTMEDIA 0
#define DENY_DIRECTMEDIA 1


#ifndef INADDR_NONE
#define INADDR_NONE (in_addr_t)(-1)
#endif

/*! Global jitterbuffer configuration - by default, jb is disabled
 *  \note Values shown here match the defaults shown in mgcp.conf.sample */
static struct ast_jb_conf default_jbconf =
{
	.flags = 0,
	.max_size = 200,
	.resync_threshold = 1000,
	.impl = "fixed",
	.target_extra = 40,
};
static struct ast_jb_conf global_jbconf;
static unsigned int megaco_chan_idx =0;       /*!< used in naming megaco channel */
static unsigned int megaco_chan_idx_out =0;       /*!< used in naming megaco channel */
static const char tdesc[] = "Media Gateway Control Protocol (MEGACO)";
static const char config[] = "megaco.conf";

#define MGCP_DTMF_RFC2833	(1 << 0)
#define MGCP_DTMF_INBAND	(1 << 1)
#define MGCP_DTMF_HYBRID	(1 << 2)


#define DEFAULT_MEGACO_C_PORT	2944 /*!< From RFC 2705 */
#define MGCP_MAX_PACKET		 1500 /*!< Also from RFC 2543, should sub headers tho */
#define DEFAULT_RETRANS		 1000 /*!< How frequently to retransmit */
#define MEGACO_AUDIT_RETRANS  5000

#define MAX_RETRANS		5    /*!< Try only 5 times for retransmissions */

/*! MGCP rtp stream modes { */
#define MGCP_CX_SENDONLY	0
#define MGCP_CX_RECVONLY	1
#define MGCP_CX_SENDRECV	2
#define MGCP_CX_CONF		3
#define MGCP_CX_CONFERENCE	3
#define MGCP_CX_MUTE		4
#define MGCP_CX_INACTIVE	4
/*! } */

static const char * const mgcp_cxmodes[] = {
	"sendonly",
	"recvonly",
	"sendrecv",
	"confrnce",
	"inactive"
};

enum {
	MGCP_CMD_EPCF,
	MGCP_CMD_CRCX,
	MGCP_CMD_MDCX,
	MGCP_CMD_DLCX,
	MGCP_CMD_RQNT,
	MGCP_CMD_NTFY,
	MGCP_CMD_AUEP,
	MGCP_CMD_AUCX,
	MGCP_CMD_RSIP
};

enum {
	MEGACO_NOTIFY,
	MEGACO_SUBTRACT,
	MEGACO_MODIFY,
	MEGACO_ADD,
	MEGACO_SERVICECHANGE,
	MEGACO_ERROR,
	MEGACO_SERVICECHANGE_WITHK,
	MEGACO_RSPACK,
	MEGACO_AUDIT,

	MEGACO_UNKNOWNCMD
};

enum {
	MEGACO_OFFHOOK_EV,
	MEGACO_ONHOOK_EV,
	MEGACO_DIALDIGIT_EV,
	MEGACO_FLASHDETECT_EV,
	MEGACO_ALLIVECHECK_EV,
	MEGACO_UNKNOWNEVENT
};
enum {
	MEGACO_IDLE_ST,     //0
	MEGACO_WFDIGIT_ST,  //1
	MEGACO_WFANSWER_ST, //2
	MEGACO_ANSWER_ST,   //3

	MEGACO_RING_ST,  //4
	//call state for incomming from sip suers
		MEGACO_SIP_WFRINGACK_ST,//5
		MEGACO_SIP_WFANSWER_ST,//6
		MEGACO_SIP_ANSWER_ST,  //7  if(sub->parent->callstate == MEGACO_SIP_ANSWER_ST )
		MEGACO_SIP_HOLD_ST,    //8
	//call from MG to SIP user
		MEGACO_MG_WFRINGACK_ST,
		MEGACO_MG_WFANSWER_ST,
		MEGACO_MG_ANSWER_ST,

	MEGACO_WFONHOOK_ST,
	MG_AWAIT_INIT_OK_ST,
	MG_ALLIVE_ST,
	MG_BROKEN_ST,
	MEGACO_CALL_WAITING_ST,
};
enum{
		MEGACO_LOCAL_CALL_TYPE,
		MEGACO_EXTERNAL_CALL_TYPE,
		MEGACO_NATIONAL_CALL_TYPE,
		MEGACO_INVALID_CALL_TYPE
};

static char context[AST_MAX_EXTENSION] = "default";
static char domain[128] = "ava-mgc.com";
static char predgt[128] = "2222";
static char dmap[256] = "28xxxxxx";
static char mg_version[16] = "2";
static char mg_mode[16] = "default";


static char language[MAX_LANGUAGE] = "";
static char musicclass[MAX_MUSICCLASS] = "";
static char parkinglot[AST_MAX_CONTEXT];
static char cid_num[AST_MAX_EXTENSION] = "";
static char cid_name[AST_MAX_EXTENSION] = "";

static int dtmfmode = 0;
static int nat = 0;
static int ncs = 0;
static int pktcgatealloc = 0;
static int hangupongateremove = 0;

static ast_group_t cur_callergroup = 0;
static ast_group_t cur_pickupgroup = 0;

static struct {
	unsigned int tos;
	unsigned int tos_audio;
	unsigned int cos;
	unsigned int cos_audio;
} qos = { 0, 0, 0, 0 };

static int immediate = 0;

static int callwaiting = 0;

static int callreturn = 0;

static int slowsequence = 0;

static int threewaycalling = 0;

/*! This is for flashhook transfers */
static int transfer = 0;

static int cancallforward = 0;

static int singlepath = 0;

static int directmedia = DIRECTMEDIA;

static char accountcode[AST_MAX_ACCOUNT_CODE] = "";

static char mailbox[AST_MAX_EXTENSION];

static int amaflags = 0;

static int adsi = 0;

static unsigned int oseq;
static unsigned int oseq_global = 0;
AST_MUTEX_DEFINE_STATIC(oseq_lock);

/*! Wait up to 16 seconds for first digit (FXO logic) */
static int firstdigittimeout = 16000;

/*! How long to wait for following digits (FXO logic) */
static int gendigittimeout = 8000;

/*! How long to wait for an extra digit, if there is an ambiguous match */
static int matchdigittimeout = 3000;

/*! Protect the monitoring thread, so only one process can kill or start it, and not
    when it's doing something critical. */
AST_MUTEX_DEFINE_STATIC(netlock);

AST_MUTEX_DEFINE_STATIC(monlock);

/*! This is the thread for the monitor which checks for input on the channels
 *  which are not currently in use.
 */
static pthread_t monitor_thread = AST_PTHREADT_NULL;

static int restart_monitor(void);

static struct ast_format_cap *global_capability;
static int nonCodecCapability = AST_RTP_DTMF;

static char ourhost[MAXHOSTNAMELEN];
static struct in_addr __ourip;
static int ourport;

static int mgcpdebug = 0;
static int megaco_req_id=500;
static struct ast_sched_context *sched;
static struct io_context *io;
/*! The private structures of the mgcp channels are linked for
 * selecting outgoing channels
 */

#define MGCP_MAX_HEADERS	64
#define MGCP_MAX_LINES		64

struct megaco_request {
	int len;
	char *verb;
	char *identifier;
	char *endpoint;
	char *version;
	int headers;			/*!< MGCP Headers */
	char *header[MGCP_MAX_HEADERS];
	int lines;			/*!< SDP Content */
	char *line[MGCP_MAX_LINES];
	char data[MGCP_MAX_PACKET];
	int cmd;                        /*!< int version of verb = command */
	int al_event;
	int transactionFlag;

	char transactionIDtext[128];
	char replyId[128];
	char contextId[128];
	char notifyId[128],observedEventsId[128],eventId[256],ephermalId[256],rtpLparam[256];
	char servicechangeId[128];
	char modifyId[128];
	char destId[128];
	char errorId[128];
	char kvalueId[128];
	unsigned int trid;              /*!< int version of identifier = transaction id */
	struct sockaddr_in sin;
	struct megaco_request *next;      /*!< next in the queue */
};

/*! \brief megaco_message: MGCP message for queuing up */
struct megaco_message {
	struct megaco_users *owner_ep;
	struct megaco_subchannel *owner_sub;
	int retrans;
	unsigned long expire;
	unsigned int seqno;
	int len;
	struct megaco_message *next;
	char buf[0];
};

#define RESPONSE_TIMEOUT 30	/*!< in seconds */

struct megaco_response {
	time_t whensent;
	int len;
	int seqno;
	struct megaco_response *next;
	char buf[0];
};

#define MAX_SUBS 2

#define SUB_REAL 0
#define SUB_ALT  1

struct megaco_subchannel {
	/*! subchannel magic string.
	   Needed to prove that any subchannel pointer passed by asterisk
	   really points to a valid subchannel memory area.
	   Ugly.. But serves the purpose for the time being.
	 */
#define megaco_subchannel_MAGIC "!978!"
	char magic[6];
	ast_mutex_t lock;
	int id;
	int sch_id;
	int AuditRetansCount;
	struct ast_channel *owner;
	//struct ast_channel *owner_hold; //comment by mkmtest960420
	struct megaco_users *parent;
	struct ast_rtp_instance *rtp;
	//struct ast_rtp_instance *rtp_hold; //comment by mkmtest960420
	
	struct sockaddr_in  rtp_remote_sin;
	int moh_port;
	struct sockaddr_in tmpdest;
	char txident[80]; /*! \todo FIXME txident is replaced by rqnt_ident in endpoint.
			This should be obsoleted */
	char cxident[80];
	char callid[64];char callid1[64];
    unsigned char cid_byte[64],cid_len;
	int cxmode;
	struct megaco_request *cx_queue; /*!< pending CX commands */
	ast_mutex_t cx_queue_lock;     /*!< CX queue lock */
	int nat;
	int iseq;                      /*!< Not used? RTP? */
	int outgoing;
	int alreadygone;
	int sdpsent;

	struct ast_channel *direct_peer; // remember two side of calls
	int peyvast;
	struct cops_gate *gate;
	struct megaco_subchannel *next;  /*!< for out circular linked list */
};

#define MGCP_ONHOOK  1
#define MGCP_OFFHOOK 2

#define TYPE_TRUNK 1
#define TYPE_LINE  2

struct megaco_users {
	ast_mutex_t lock;
	char name[80];
	char telNo[80];
	struct megaco_subchannel *sub;		/*!< Pointer to our current connection, channel and stuff */
	char accountcode[AST_MAX_ACCOUNT_CODE];
	char exten[AST_MAX_EXTENSION];		/*!< Extention where to start */
	char context[AST_MAX_EXTENSION];
	char language[MAX_LANGUAGE];
	char cid_num[AST_MAX_EXTENSION];	/*!< Caller*ID number */
	char cid_name[AST_MAX_EXTENSION];	/*!< Caller*ID name */
	char lastcallerid[AST_MAX_EXTENSION];	/*!< Last Caller*ID */
	char dtmf_buf[AST_MAX_EXTENSION];	/*!< place to collect digits be */
	char call_forward[AST_MAX_EXTENSION];	/*!< Last Caller*ID */
	char musicclass[MAX_MUSICCLASS];
	char curtone[80];			/*!< Current tone */
	char mailbox[AST_MAX_EXTENSION];
	char parkinglot[AST_MAX_CONTEXT];   /*!< Parkinglot */
	struct ast_event_sub *mwi_event_sub;
	ast_group_t callgroup;
	ast_group_t pickupgroup;
	int callwaiting;
	int hascallwaiting;
	int transfer;
	int threewaycalling;
	int singlepath;
	int cancallforward;
	int directmedia;
	int callreturn;
	int dnd; /* How does this affect callwait? Do we just deny a megaco_request if we're dnd? */
	int hascallerid;
	int hidecallerid;
	int dtmfmode;
	int amaflags;
	int ncs;
	int pktcgatealloc;
	int hangupongateremove;
	int type;
	int slowsequence;			/*!< MS: Sequence the endpoint as a whole */
	int group;
	int iseq; /*!< Not used? */
	int lastout; /*!< tracking this on the subchannels.  Is it needed here? */
	int needdestroy; /*!< Not used? */
	struct ast_format_cap *cap;
	int nonCodecCapability;
	int onhooktime;
	int msgstate; /*!< voicemail message state */
	int immediate;
	int hookstate;
	int adsi;
	int callstate;
	int iscallwaiting;
	int falshcnt;
	int calltype;
	char contextId[128];
	char destId[128];
	struct sockaddr_in destIp_addr;
	char ephermalId[128];
	char rtpLparam[128];
	char rqnt_ident[80];             /*!< request identifier */
	struct megaco_request *rqnt_queue; /*!< pending RQNT commands */
	ast_mutex_t rqnt_queue_lock;
	struct megaco_request *cmd_queue;  /*!< pending commands other than RQNT */
	ast_mutex_t cmd_queue_lock;
	int delme;                       /*!< needed for reload */
	int needaudit;                   /*!< needed for reload */
	struct ast_dsp *dsp; /*!< XXX Should there be a dsp/subchannel? XXX */
	/* owner is tracked on the subchannels, and the *sub indicates whos in charge */
	/* struct ast_channel *owner; */
	/* struct ast_rtp *rtp; */
	/* struct sockaddr_in tmpdest; */
	/* message go the the endpoint and not the channel so they stay here */
	struct ast_variable *chanvars;		/*!< Variables to set for channel created by user */
	struct megaco_users *next;
	struct megaco_mg *parent;
};

static struct megaco_mg {
	/* A MG  containing one or more users */
	char name[80];
	char domain[128];
	char predgt[128];
	char dmap[256];
	char mg_version[16];
	char mg_mode[16];   //defualt,huawei,zte,opnet,keymile,zyxel
	int isnamedottedip; /*!< is the name FQDN or dotted ip */
	struct sockaddr_in addr;
	struct sockaddr_in defaddr;
	struct in_addr ourip;
	int dynamic;
	int expire;		/*!< XXX Should we ever expire dynamic registrations? XXX */
	struct megaco_users *endpoints;
	struct ast_ha *ha;
/* obsolete
	time_t lastouttime;
	int lastout;
	int messagepending;
*/
/* Wildcard endpoint name */
	char wcardep[30];
	struct megaco_message *msgs; /*!< gw msg queue */
	ast_mutex_t msgs_lock;     /*!< queue lock */
	int retransid;             /*!< retrans timer id */
	int delme;                 /*!< needed for reload */
	int realtime;
	struct megaco_response *responses;
	struct megaco_mg *next;
} *megacomg = NULL;

AST_MUTEX_DEFINE_STATIC(mgcp_reload_lock);
static int mgcp_reloading = 0;

/*! \brief gatelock: mutex for gateway/endpoint lists */
AST_MUTEX_DEFINE_STATIC(gatelock);

static int mgcpsock  = -1;

struct sockaddr_in sin_temp;


static struct sockaddr_in bindaddr;
//static int buildServiceChangeReply(char *h,unsigned int transactionId, char *terminationId, char *contextId);

static int transmit_response(struct megaco_subchannel *sub, char *msg, struct megaco_request *req, char *msgrest);
static int transmit_notify_request(struct megaco_subchannel *sub, char *tone);
static int transmit_modify_request(struct megaco_subchannel *sub);
static int transmit_connect(struct megaco_subchannel *sub);
static int transmit_modify_with_sdp(struct megaco_subchannel *sub, struct ast_rtp_instance *rtp, const struct ast_format_cap *codecs);
static int transmit_connection_del(struct megaco_subchannel *sub);
static int transmit_audit_endpoint(struct megaco_users *p);
static void megaco_start_rtp(struct megaco_subchannel *sub,struct ast_rtp_instance *rtp);
static void megaco_parse(struct megaco_request *req,int  mg_type);

static void dump_cmd_queues(struct megaco_users *p, struct megaco_subchannel *sub);
static char *mgcp_reload(struct ast_cli_entry *e, int cmd, struct ast_cli_args *a);
static int reload_config(int reload);

static struct ast_channel *megaco_request_call(const char *type, struct ast_format_cap *cap, const struct ast_channel *requestor, const char *dest, int *cause);
static int megaco_call(struct ast_channel *ast, const char *dest, int timeout);
static int megaco_hangup(struct ast_channel *ast);
static int megaco_answer(struct ast_channel *ast);
static struct ast_frame *megaco_read(struct ast_channel *ast);
static int megaco_write(struct ast_channel *ast, struct ast_frame *frame);
static int megaco_indicate(struct ast_channel *ast, int ind, const void *data, size_t datalen);
static int megaco_fixup(struct ast_channel *oldchan, struct ast_channel *newchan);
static int mgcp_senddigit_begin(struct ast_channel *ast, char digit);
static int mgcp_senddigit_end(struct ast_channel *ast, char digit, unsigned int duration);
static int megaco_devicestate(const char *data);
static void add_header_offhook(struct megaco_subchannel *sub, struct megaco_request *resp, char *tone);

static struct megaco_mg *build_gateway(char *cat, struct ast_variable *v);
static int acf_channel_read(struct ast_channel *chan, const char *funcname, char *preparse, char *buf, size_t buflen);
static struct ast_variable *add_var(const char *buf, struct ast_variable *list);
static struct ast_variable *copy_vars(struct ast_variable *src);
static int transmit_notify_resp(struct megaco_request *req,struct megaco_subchannel *sub);
  //megaco functions  added by mkm
static int transmit_serviceChangeReply(struct megaco_request *req,int kflag,struct megaco_subchannel *sub);
//static int transmit_serviceChangeToMg(struct megaco_request *req,int kflag);
static int transmit_ModifyOffhookDialTone(struct megaco_request *req,struct megaco_subchannel *sub);
static int transmit_ModifyToChekOffhook(struct megaco_request *req,char *contextId,char *modifyId,struct megaco_subchannel *sub);
//*********  tone generator
static int transmit_ModifyBusyTone(char *contextId,char *notifyId,struct megaco_subchannel *sub);
static int transmit_ModifyCongestionTone(struct megaco_request *req,struct megaco_subchannel *sub);
static int transmit_ModifySpecialInformationTone(struct megaco_request *req,struct megaco_subchannel *sub);
static int transmit_ModifyPayPhoneRinginigTone(struct megaco_request *req,struct megaco_subchannel *sub);
static int transmit_ModifyWarningTone(struct megaco_request *req,struct megaco_subchannel *sub);
static int transmit_ModifyCallerWaitingTone(struct megaco_request *req,struct megaco_subchannel *sub);
static int transmit_ModifyCallWaitingTone(char *contextId,char *notifyId,struct megaco_subchannel *sub);
//**********************
static int transmit_ModifyPlayAnnouncment(struct megaco_request *req,struct megaco_subchannel *sub);
static int transmit_ModifyRingBackTone(struct megaco_request *req,struct megaco_subchannel *sub);
static int transmit_ModifyRingBackTone1(char *contextId,char *notifyId, struct megaco_subchannel *sub);
static int transmit_ModifyRing(struct megaco_request *req,struct megaco_subchannel *sub);
static int transmit_AddChooseOutgoing(struct megaco_request *req,char *destId,struct megaco_subchannel *sub);
static int transmit_AddSipChooseOutgoing(struct megaco_request *req,char *destId,struct megaco_subchannel *sub);
static int transmit_ModifyTdmNoSignal(struct megaco_request *req,char *contextId,char *notifyId,struct megaco_subchannel *sub);
static int transmit_ModifyTdmNoSignalWithSDP(struct megaco_request *req,char *contextId,char *notifyId,struct megaco_subchannel *sub,struct megaco_subchannel *b_sub);
static int transmit_ModifyTdmNoSignalWithSDP_1(struct megaco_request *req,char *contextId,char *notifyId,struct megaco_subchannel *sub,struct megaco_subchannel *b_sub);
static int transmit_ModifyTdmNoSignalWithSDP_2(struct megaco_request *req,char *contextId,char *notifyId,struct megaco_subchannel *sub,struct megaco_subchannel *b_sub);
static int transmit_connectAB(struct megaco_request *req,char *AnotifyId,char *AcontextId,char *BnotifyId,char *BcontextId);
static int transmit_SubtractAllContext(struct megaco_request *req,char *contextId,struct megaco_subchannel *sub);
static int add_header_i(struct megaco_request *req, const char *var, unsigned int value);
static int add_header_n1(struct megaco_request *req, const char *var, const char *value);
static int digit_analyze(struct megaco_request *req,struct megaco_subchannel *sub);
static int sip_find_mg_dest(char *name,struct sockaddr_in *sin);
static int find_mg_user_call_state(char *name);
static int reset_mg_user_call_state(char *name);
static struct megaco_subchannel *find_subchannel_and_lock(char *name, int msgid, struct sockaddr_in *sin);
static void megaco_get_remote_param(char *terminationId,struct sockaddr_in *sin_in);
//static void megaco_get_remote_paramfromholdchannel(char *terminationId,struct sockaddr_in *sin_in);
static int transmit_ModifyPalyCrbt(struct megaco_request *req,char *contextId,char *notifyId,struct megaco_subchannel *sub,struct megaco_subchannel *b_sub);
/* modified for the new transaction mechanism */
static int megaco_postrequest(struct megaco_users *p, struct megaco_subchannel *sub, char *data, int len, unsigned int seqno);
static int transmit_MgCheckAlliveMGC(struct megaco_subchannel *sub);
static int transmit_ModifyAll(char *contextId,char *notifyId,struct sockaddr_in *sin);
static int transmit_ModifyOneSubChannel(char *contextId,char *name, struct megaco_subchannel *sub);
static int transmit_AuditRoot(struct megaco_subchannel *sub);
static int transmit_InitailAllTermination(struct megaco_request *req,struct sockaddr_in *sin);
static int publish_expire(const void *data);
static int transmit_MgAuditRoot(struct megaco_subchannel *sub);
static struct ast_channel *megaco_new(struct megaco_subchannel *sub, int state, const char *linkedid,int mojtaba);
static char *megacostate2str(int state) ;

static struct ast_channel_tech mgcp_tech = {
	.type ="MEGACO", //"MGCP",
	.description = tdesc,
	.properties = AST_CHAN_TP_WANTSJITTER | AST_CHAN_TP_CREATESJITTER,
	.requester = megaco_request_call,
	.devicestate = megaco_devicestate,
	.call = megaco_call,
	.hangup = megaco_hangup,
	.answer = megaco_answer,
	.read = megaco_read,
	.write = megaco_write,
	.indicate = megaco_indicate,
	.fixup = megaco_fixup,
	.send_digit_begin = mgcp_senddigit_begin,
	.send_digit_end = mgcp_senddigit_end,
	.bridge = ast_rtp_instance_bridge,
	.func_channel_read = acf_channel_read,
};

static void mwi_event_cb(const struct ast_event *event, void *userdata)
{
	/* This module does not handle MWI in an event-based manner.  However, it
	 * subscribes to MWI for each mailbox that is configured so that the core
	 * knows that we care about it.  Then, chan_mgcp will get the MWI from the
	 * event cache instead of checking the mailbox directly. */
}

static int has_voicemail(struct megaco_users *p)
{
	int new_msgs;
	struct ast_event *event;
	char *mbox, *cntx;

	cntx = mbox = ast_strdupa(p->mailbox);
	strsep(&cntx, "@");
	if (ast_strlen_zero(cntx))
		cntx = "default";

	event = ast_event_get_cached(AST_EVENT_MWI,
		AST_EVENT_IE_MAILBOX, AST_EVENT_IE_PLTYPE_STR, mbox,
		AST_EVENT_IE_CONTEXT, AST_EVENT_IE_PLTYPE_STR, cntx,
		AST_EVENT_IE_END);

	if (event) {
		new_msgs = ast_event_get_ie_uint(event, AST_EVENT_IE_NEWMSGS);
		ast_event_destroy(event);
	} else
		new_msgs = ast_app_has_voicemail(p->mailbox, NULL);

	return new_msgs;
}

static int unalloc_sub(struct megaco_subchannel *sub)
{
	struct megaco_users *p = sub->parent;
	if (p->sub == sub) {
		ast_log(LOG_WARNING, "Trying to unalloc the real channel %s@%s?!?\n", p->name, p->parent->name);
		return -1;
	}
	ast_debug(1, "Released sub %d of channel %s@%s\n", sub->id, p->name, p->parent->name);

	sub->owner = NULL;
	
	//sub->owner_hold = NULL;////comment by mkmtest960420

	if (!ast_strlen_zero(sub->cxident)) {
		transmit_connection_del(sub);
	}
	sub->cxident[0] = '\0';
	sub->callid[0] = '\0';
	sub->cxmode = MGCP_CX_INACTIVE;
	sub->outgoing = 0;
	sub->alreadygone = 0;
	memset(&sub->tmpdest, 0, sizeof(sub->tmpdest));
	if (sub->rtp) {
		ast_rtp_instance_destroy(sub->rtp);
		sub->rtp = NULL;
	}
	/*if (sub->rtp_hold) {
		ast_rtp_instance_destroy(sub->rtp_hold);
		sub->rtp_hold = NULL;
	}*/
	dump_cmd_queues(NULL, sub);
	return 0;
}

/* modified for new transport mechanism */
static int __mgcp_xmit(struct megaco_mg *gw, char *data, int len)
{

	int res;
	ast_verb(3,"-----------megaco_xmit :%s \n",data);

	if (gw->addr.sin_addr.s_addr)
		res=sendto(mgcpsock, data, len, 0, (struct sockaddr *)&gw->addr, sizeof(struct sockaddr_in));
	else
		res=sendto(mgcpsock, data, len, 0, (struct sockaddr *)&gw->defaddr, sizeof(struct sockaddr_in));
	if (res != len) {
		ast_log(LOG_WARNING, ",megaco_xmit returned %d: %s\n", res, strerror(errno));
	}
	return res;
}

static int resend_response(struct megaco_subchannel *sub, struct megaco_response *resp)
{
	struct megaco_users *p = sub->parent;
	int res;
	ast_debug(1, "Retransmitting:\n%s\n to %s:%d\n", resp->buf, ast_inet_ntoa(p->parent->addr.sin_addr), ntohs(p->parent->addr.sin_port));
	res = __mgcp_xmit(p->parent, resp->buf, resp->len);
	if (res > 0)
		res = 0;
	return res;
}

static int send_response(struct megaco_subchannel *sub, struct megaco_request *req)
{
	struct megaco_users *p = sub->parent;
	int res;
	ast_debug(1, "Transmitting:\n%s\n to %s:%d\n", req->data, ast_inet_ntoa(p->parent->addr.sin_addr), ntohs(p->parent->addr.sin_port));
	res = __mgcp_xmit(p->parent, req->data, req->len);
	if (res > 0)
		res = 0;
	return res;
}

/* modified for new transport framework */
static void dump_queue(struct megaco_mg *gw, struct megaco_users *p)
{
	struct megaco_message *cur, *q = NULL, *w, *prev;

		ast_mutex_lock(&gw->msgs_lock);
		for (prev = NULL, cur = gw->msgs; cur; prev = cur, cur = cur->next) {
			if (!p || cur->owner_ep == p) {
				if (prev) {
					prev->next = cur->next;
				} else {
					gw->msgs = cur->next;
				}

				ast_log(LOG_NOTICE, "Removing message from %s transaction %u\n",
					gw->name, cur->seqno);

				w = cur;
				if (q) {
					w->next = q;
				} else {
					w->next = NULL;
				}
				q = w;
			}
		}
		ast_mutex_unlock(&gw->msgs_lock);

		while (q) {
			cur = q;
			q = q->next;
			ast_free(cur);
		}
}

static void mgcp_queue_frame(struct megaco_subchannel *sub, struct ast_frame *f)
{
	for (;;) {
		if (sub->owner) {
			if (!ast_channel_trylock(sub->owner)) {
				ast_queue_frame(sub->owner, f);
				ast_channel_unlock(sub->owner);
				break;
			} else {
				DEADLOCK_AVOIDANCE(&sub->lock);
			}
		} else {
			break;
		}
	}
}

static void mgcp_queue_hangup(struct megaco_subchannel *sub)
{
	for (;;) {
			if (sub->owner) {
				if (!ast_channel_trylock(sub->owner)) {
					ast_queue_hangup(sub->owner);
					ast_channel_unlock(sub->owner);
					break;
				} else {
					DEADLOCK_AVOIDANCE(&sub->lock);
				}
			} else {
				break;
			}
		}
}

static void mgcp_queue_control(struct megaco_subchannel *sub, int control)
{
	struct ast_frame f = { AST_FRAME_CONTROL, { control } };
	return mgcp_queue_frame(sub, &f);
}

/* modified for the new transaction mechanism */
static int megaco_postrequest(struct megaco_users *p, struct megaco_subchannel *sub,
                            char *data, int len, unsigned int seqno)
{
	struct megaco_message *msg;
	struct megaco_message *cur;
	struct megaco_mg *gw;
	struct timeval now;
    ast_verb(3,"--------megaco_postrequest \n");

	if (!(msg = ast_malloc(sizeof(*msg) + len))) {
		return -1;
	}
	if (!(gw = ((p && p->parent) ? p->parent : NULL))) {
		ast_free(msg);
		return -1;
	}

	msg->owner_sub = sub;
	msg->owner_ep = p;
	msg->seqno = seqno;
	msg->next = NULL;
	msg->len = len;
	msg->retrans = 0;
	memcpy(msg->buf, data, msg->len);

	ast_mutex_lock(&gw->msgs_lock);
	for (cur = gw->msgs; cur && cur->next; cur = cur->next);
	if (cur) {
		cur->next = msg;
	} else {
		gw->msgs = msg;
	}

	now = ast_tvnow();
	msg->expire = now.tv_sec * 1000 + now.tv_usec / 1000 + DEFAULT_RETRANS;
/*
	if (gw->retransid == -1)
		gw->retransid = ast_sched_add(sched, DEFAULT_RETRANS, retrans_pkt, (void *)gw);
*/
	ast_mutex_unlock(&gw->msgs_lock);


	//__mgcp_xmit(gw, msg->buf, msg->len);?????? comment for test mg94-06-04

	/* XXX Should schedule retransmission XXX */
	return 0;
}

static int megaco_call(struct ast_channel *ast, const char *dest, int timeout)
{
	int res;
	struct megaco_users *p;
	struct megaco_subchannel *sub;
	//char tone[50] = "";
	const char *distinctive_ring = NULL;
	struct varshead *headp;
	struct ast_var_t *current;

	ast_log(LOG_WARNING, "Incomming sip megaco_call(%s)\n", ast_channel_name(ast));

	sub = ast_channel_tech_pvt(ast);
	p = sub->parent;
	headp = ast_channel_varshead(ast);
	AST_LIST_TRAVERSE(headp,current,entries) {
	/* Check whether there is an ALERT_INFO variable */
	if (strcasecmp(ast_var_name(current),"ALERT_INFO") == 0) {
		distinctive_ring = ast_var_value(current);
		}
	}
	ast_mutex_lock(&sub->lock);

	if ((ast_channel_state(ast) != AST_STATE_DOWN) && (ast_channel_state(ast) != AST_STATE_RESERVED)) {
	    ast_log(LOG_WARNING, "megaco_call called on %s, neither down nor reserved\n", ast_channel_name(ast));
	    ast_mutex_unlock(&sub->lock);
		return -1;
	}

	res = 0;
	sub->outgoing = 1;
	sub->cxmode = MGCP_CX_RECVONLY;
	ast_setstate(ast, AST_STATE_RINGING);

			
	//if (p->type == TYPE_LINE)
	// {
		if (!sub->rtp)
	    {
			megaco_start_rtp(sub,sub->rtp);
		} 
		else
		{
			ast_log(LOG_WARNING,"megaco_call :%s   RTP pointer error \n",p->name);
		}
			//remian for usage of function prototype late
			//S_COR(ast_channel_connected(ast)->id.number.valid, ast_channel_connected(ast)->id.number.str, ""),

	 // } 
	 // else 
	 // {
	//		ast_log(LOG_NOTICE, "Don't know how to dial on trunks yet\n");
	//		res = -1;
	 // }
			ast_mutex_unlock(&sub->lock);

	return res;
}

static int megaco_hangup(struct ast_channel *ast)
{
	struct megaco_subchannel *sub = ast_channel_tech_pvt(ast);
	struct megaco_users *p = sub->parent;
	struct ast_channel *bridged;

    ast_log(LOG_WARNING,"megaco_hangup(%s)<%s> State:%s\n", ast_channel_name(ast),p->contextId,megacostate2str(p->callstate));

	if (!ast_channel_tech_pvt(ast)) {
			ast_debug(1, "Asked to hangup channel not connected\n");
			return 0;
		}
		if (strcmp(sub->magic, megaco_subchannel_MAGIC)) {
			ast_debug(1, "Invalid magic. MEGACO subchannel freed up already.\n");
			return 0;
		}
		ast_mutex_lock(&sub->lock);
		sub->owner = NULL;
			    //comment by mkmtest960420 
			           /*
        if(sub->owner) 
        {
	        if(ast_channel_name(ast) == ast_channel_name(sub->owner))
	        {
				sub->owner = NULL;
			}
			else
			{

				if(sub->owner_hold)
				{
					if(ast_channel_name(ast) == ast_channel_name(sub->owner_hold))
					{
					    sub->owner_hold = NULL;
					}
					else
					{
					    ast_log(LOG_WARNING, "Megaco_hangup  %s not valid\n", ast_channel_name(ast));
					    ast_verb(3, "Megaco_hangup  %s not valid\n", ast_channel_name(ast));
						return 0;
					}
				}
				//comment by mkmtest960420
				
				ast_log(LOG_WARNING, "Hangup channel wasn't %s but was %s\n", ast_channel_name(ast), ast_channel_name(sub->owner));
  		    }
  		}*/
		//ast_verb(3,"megaco_hangup2 ContextID :%s callState:%s channel_name :%s \n",p->contextId,megacostate2str(p->callstate),ast_channel_name(ast));
		//must free all of resource

        if(p->callstate != MEGACO_IDLE_ST)
        {
			//transmit_SubtractAllContext(NULL,p->contextId,sub);
		//	memset(sub->parent->contextId,0,sizeof(sub->parent->contextId));
			switch(p->callstate)
			{
				case MEGACO_MG_ANSWER_ST:
				case MEGACO_SIP_ANSWER_ST:
					//comment by mkmtest960420
				/*	if(sub->parent->iscallwaiting ==1)
					{
							ast_verb(3,"Megaco :%s  come out from waiting \n",p->name);
				            p->callstate = MEGACO_SIP_ANSWER_ST;
				            p->iscallwaiting =0;
						    ast_channel_tech_pvt_set(ast, NULL);

							if (sub->rtp_hold) {
								ast_verb(3,"distroy  hold rtp for Megaco :%s\n",p->name);
								ast_rtp_instance_destroy(sub->rtp_hold);
								sub->rtp_hold = NULL;
							}			            
						    ast_module_unref(ast_module_info->self);
							ast_mutex_unlock(&sub->lock);
	        				return 0;						

					}
					else*/
					//comment by mkmtest960420
					{
							transmit_ModifyBusyTone(p->contextId,sub->parent->name,sub);
							p->callstate = MEGACO_WFONHOOK_ST;
					}
				break;
				case MEGACO_WFONHOOK_ST:
						ast_verb(3,"Already sent busy and wait for onhook\n");
					break;
			case MEGACO_SIP_WFANSWER_ST:
						transmit_ModifyToChekOffhook(NULL,p->contextId,p->name,sub);
						usleep(2000);
					    transmit_SubtractAllContext(NULL,p->contextId,sub);  //keymile ad
					    p->callstate = MEGACO_IDLE_ST;
						break;
			//comment by mkmtest960420
			/*case  MEGACO_CALL_WAITING_ST:
			            ast_verb(3,"Megaco :%s  come out from waiting \n",p->name);
			            p->callstate = MEGACO_SIP_ANSWER_ST;
			            p->iscallwaiting =0;
					    ast_channel_tech_pvt_set(ast, NULL);

						if (sub->rtp_hold) {
							ast_verb(3,"distroy  hold rtp for Megaco :%s\n",p->name);
							ast_rtp_instance_destroy(sub->rtp_hold);
							sub->rtp_hold = NULL;
						}			            
					    ast_module_unref(ast_module_info->self);
						ast_mutex_unlock(&sub->lock);
        				return 0;						

			break;*/
			//comment by mkmtest960420					
				default:
					transmit_ModifyToChekOffhook(NULL,"-",p->name,sub);
					p->callstate = MEGACO_IDLE_ST;

					break;
			}
			memset(sub->parent->contextId,0,sizeof(sub->parent->contextId));
        }

		ast_channel_tech_pvt_set(ast, NULL);

		sub->alreadygone = 0;
		sub->outgoing = 0;
		sub->cxmode = MGCP_CX_INACTIVE;
		sub->callid[0] = '\0';
		if (p) {
			memset(p->dtmf_buf, 0, sizeof(p->dtmf_buf));
		}
		/* Reset temporary destination */
		memset(&sub->tmpdest, 0, sizeof(sub->tmpdest));

		if (sub->rtp) {
			ast_rtp_instance_destroy(sub->rtp);
			sub->rtp = NULL;
			ast_log(LOG_WARNING,"megaco_hangup :%s  Destroy RTP pointer \n",p->name);
		}
		else
		{
			ast_log(LOG_WARNING,"megaco_hangup :%s  Destroy RTP pointer Error \n",p->name);
		}

		ast_module_unref(ast_module_info->self);

		ast_mutex_unlock(&sub->lock);

	return 0;
}
/*
//comment by mkmtest960420
static void megaco_get_remote_paramfromholdchannel(char *terminationId,struct sockaddr_in *sin_in)
{
	struct megaco_mg  *mg;
	struct megaco_users *me;

	struct ast_channel *chan;
	struct ast_channel *bridge;
	struct megaco_subchannel *sub;
	struct sip_pvt *sip_sub;
    struct sockaddr_in sin;
	struct ast_sockaddr sin_tmp;


    ast_verb(3,"megaoc test for <%s> \n",terminationId);

    sub = find_subchannel_and_lock(terminationId, 0, sin_in);
    if(sub)
    {

    	chan=sub->owner_hold;
    	if(chan)
    	{
    		ast_verb(3,"termination ID <%s> channelName:<%s>\n",terminationId,ast_channel_name(chan));

    		if ((bridge = ast_bridged_channel(chan)))
    		{
    			ast_verb(3,"bridged termination ID <%s> channelName:<%s>\n",terminationId,ast_channel_name(bridge));
    			sip_sub = ast_channel_tech_pvt(bridge);

    			if(sip_sub)
    			{
    				//ast_verb(3,"FFFFFFFFFFFFFFFFFFFf\n");
    				//ast_rtp_instance_update_source(sub->rtp);
    				ast_rtp_instance_get_local_address(sip_sub->rtp, &sin_tmp);
    				ast_sockaddr_to_sin(&sin_tmp, &sin);
    				ast_verb(3, "We're at %s port %d\n", ast_inet_ntoa(sin.sin_addr), ntohs(sin.sin_port));
    				ast_rtp_instance_get_remote_address(sip_sub->rtp, &sin_tmp);
    			//st_sockaddr_to_sin(&sin_tmp, &sub->rtp_remote_sin);
    				sub->rtp_remote_sin.sin_port = sin.sin_port ;
    			
    				ast_verb(3, "OOOOOO megaco_get_remote_param remote at %s port %d\n", ast_inet_ntoa(sub->rtp_remote_sin.sin_addr), ntohs(sub->rtp_remote_sin.sin_port));
    			}

    		}
    	}

    }
}

*/
//comment by mkmtest960420

static void megaco_get_remote_param(char *terminationId,struct sockaddr_in *sin_in)
{
	struct megaco_mg  *mg;
	struct megaco_users *me;

	struct ast_channel *chan;
	struct ast_channel *bridge;
	struct megaco_subchannel *sub;
	struct sip_pvt *sip_sub;
    struct sockaddr_in sin;
	struct ast_sockaddr sin_tmp;


    ast_verb(3,"megaoc test for <%s> \n",terminationId);

    sub = find_subchannel_and_lock(terminationId, 0, sin_in);
    if(sub)
    {

    	chan=sub->owner;
    	if(chan)
    	{
    		ast_verb(3,"termination ID <%s> channelName:<%s>\n",terminationId,ast_channel_name(chan));

    		if ((bridge = ast_bridged_channel(chan)))
    		{
    			ast_verb(3,"bridged termination ID <%s> channelName:<%s>\n",terminationId,ast_channel_name(bridge));
    			sip_sub = ast_channel_tech_pvt(bridge);

    			if(sip_sub)
    			{
    				//ast_verb(3,"FFFFFFFFFFFFFFFFFFFf\n");
    				//ast_rtp_instance_update_source(sub->rtp);
    				ast_rtp_instance_get_local_address(sip_sub->rtp, &sin_tmp);
    				ast_sockaddr_to_sin(&sin_tmp, &sin);
    				ast_verb(3, "We're at %s port %d\n", ast_inet_ntoa(sin.sin_addr), ntohs(sin.sin_port));
    				ast_rtp_instance_get_remote_address(sip_sub->rtp, &sin_tmp);
    				ast_sockaddr_to_sin(&sin_tmp, &sub->rtp_remote_sin);
    				ast_verb(3, "megaco_get_remote_param remote at %s port %d\n", ast_inet_ntoa(sub->rtp_remote_sin.sin_addr), ntohs(sub->rtp_remote_sin.sin_port));
    			}

    		}
    	}

    }

}
static char *megaco_test(struct ast_cli_entry *e, int cmd, struct ast_cli_args *a)
{
	switch (cmd) {
	case CLI_INIT:
		e->command = "megaco show version";
		e->usage =
			"Usage: megaco show version\n"
			"       Write for show version \n";
		return NULL;
	case CLI_GENERATE:
		return NULL;
	}
  //17 is for keymule and huawei K&H
	//18  is for fiberhome
	//ast_cli(a->fd, "build by mkkm <office> Megaco-K&H Version: %02d.%02d.%02d\n",3,0,30 );
	//ast_cli(a->fd, "build by mkkm <office> FiberHome Version: %02d.%02d.%02d\n",3,0,30);
	ast_cli(a->fd, "build by mkkm <office> Automg type  Version: %02d.%02d.%02d\n",3,0,32);
	return CLI_SUCCESS;

}

static char *handle_megaco_reset_mguser(struct ast_cli_entry *e, int cmd, struct ast_cli_args *a)
{

    struct megaco_mg  *mg;
	struct megaco_users *me;
	int state = 0;

	switch (cmd) {
	case CLI_INIT:
		e->command = "megaco reset mguser";
		e->usage =
			"Usage: megaco reset mguser\n"
			"       reset state of meguser known to the MEGACO (H.248) subsystem.\n";
		return NULL;
	case CLI_GENERATE:
		return NULL;
	}
	if (a->argc <4) {
		return CLI_SHOWUSAGE;
	}
	ast_mutex_lock(&gatelock);

	ast_cli(a->fd, " Reset Will be on ::%s\n",a->argv[3]);
	if((state=reset_mg_user_call_state(a->argv[3]))>=0)
	{
		ast_cli(a->fd, " State is : %d goes IDLE\n",state);
	}
    ast_mutex_unlock(&gatelock);
	return CLI_SUCCESS;

}
static char *handle_megaco_show_mguser(struct ast_cli_entry *e, int cmd, struct ast_cli_args *a)
{

    struct megaco_mg  *mg;
	struct megaco_users *me;
	int state = 0;
	struct ast_variable * v = NULL;

	switch (cmd) {
	case CLI_INIT:
		e->command = "megaco show mguser";
		e->usage =
			"Usage: megaco show mguser\n"
			"       Lists state of meguser known to the MEGACO (H.248) subsystem.\n";
		return NULL;
	case CLI_GENERATE:
		return NULL;
	}
	if (a->argc <4) {
		return CLI_SHOWUSAGE;
	}
	ast_mutex_lock(&gatelock);
	//ast_cli(a->fd, "  Variables::%s\n",a->argv[3]);
	if((state=find_mg_user_call_state(a->argv[3]))>=0)
	{
		//ast_cli(a->fd, "  Variables::%s::%d\n",a->argv[3],state);

		ast_cli(a->fd, "%d\n",state);
	}
    ast_mutex_unlock(&gatelock);
	return CLI_SUCCESS;

}
static int find_ag_type(char *e)
{
	struct megaco_mg  *mg;
	
	for (mg = megacomg; mg; mg = mg->next) {
		
		if(strcasecmp(e,ast_inet_ntoa(mg->addr.sin_addr))==0)
		{
			//ast_verb(3,"find_ag_type:%s <%s> %d\n",e,ast_inet_ntoa(mg->addr.sin_addr),atoi(mg->mg_mode));	
			return atoi(mg->mg_mode);
		}
		//else
			//ast_verb(3,"next_ag_type:%s  <%s>\n",e,ast_inet_ntoa(mg->addr.sin_addr));
		
	}
		
	return 0xff; //not find  any mg type
}

static char *handle_megaco_show_megacomg(struct ast_cli_entry *e, int cmd, struct ast_cli_args *a)
{
	struct megaco_mg  *mg;
	struct megaco_users *me;
	int hasendpoints = 0;
	struct ast_variable * v = NULL;

	switch (cmd) {
	case CLI_INIT:
		e->command = "megaco show mgusers";
		e->usage =
			"Usage: megaco show megacomg\n"
			"       Lists all megacomg known to the MEGACO (H.248) subsystem.\n";
		return NULL;
	case CLI_GENERATE:
		return NULL;
	}

	if (a->argc != 3) {
		return CLI_SHOWUSAGE;
	}
	//find_ag_type("172.20.229.1");
	
	ast_mutex_lock(&gatelock);
	for (mg = megacomg; mg; mg = mg->next) {
		ast_cli(a->fd, "Gateway '%s':%s	 at %s (%s%s)\n", mg->name,mg->domain, mg->addr.sin_addr.s_addr ? ast_inet_ntoa(mg->addr.sin_addr) : ast_inet_ntoa(mg->defaddr.sin_addr), mg->realtime ? "Realtime, " : "", mg->dynamic ? "Dynamic" : "Static");
		for (me = mg->endpoints; me; me = me->next) {
			ast_cli(a->fd, "   -- '<%s>%s@%s in '%s' is %s callstate:%d %s predgt:%s dmap:%s \n", me->telNo, me->name, mg->name, me->context, me->sub->owner ? "active" : "idle",me->callstate,
					me->parent->domain,me->parent->predgt,me->parent->dmap);
			if (me->chanvars) {
				ast_cli(a->fd, "  Variables:\n");
				for (v = me->chanvars ; v ; v = v->next) {
					ast_cli(a->fd, "    %s = '%s'\n", v->name, v->value);
				}
			}
			hasendpoints = 1;
		}
		if (!hasendpoints) {
			ast_cli(a->fd, "   << No Endpoints Defined >>     ");
		}
	}
	ast_mutex_unlock(&gatelock);
	
	
	
	return CLI_SUCCESS;
}

static char *handle_megaco_audit_endpoint(struct ast_cli_entry *e, int cmd, struct ast_cli_args *a)
{
	struct megaco_mg  *mg;
	struct megaco_users *me;
	int found = 0;
	char *ename,*gname, *c;

	switch (cmd) {
	case CLI_INIT:
		e->command = "megaco audit endpoint";
		e->usage =
			"Usage: megaco audit endpoint <endpointid>\n"
			"       Lists the capabilities of an endpoint in the MEGACO (H.248 Protocol) subsystem.\n"
			"       megaco debug MUST be on to see the results of this command.\n";
		return NULL;
	case CLI_GENERATE:
		return NULL;
	}

	if (!mgcpdebug) {
		return CLI_SHOWUSAGE;
	}
	if (a->argc != 4)
		return CLI_SHOWUSAGE;
	/* split the name into parts by null */
	ename = ast_strdupa(a->argv[3]);
	for (gname = ename; *gname; gname++) {
		if (*gname == '@') {
			*gname = 0;
			gname++;
			break;
		}
	}
	if (gname[0] == '[') {
		gname++;
	}
	if ((c = strrchr(gname, ']'))) {
		*c = '\0';
	}
	ast_mutex_lock(&gatelock);
	for (mg = megacomg; mg; mg = mg->next) {
		if (!strcasecmp(mg->name, gname)) {
			for (me = mg->endpoints; me; me = me->next) {
				if (!strcasecmp(me->name, ename)) {
					found = 1;
					transmit_audit_endpoint(me);
					break;
				}
			}
			if (found) {
				break;
			}
		}
	}
	if (!found) {
		ast_cli(a->fd, "   << Could not find endpoint >>     ");
	}
	ast_mutex_unlock(&gatelock);
	return CLI_SUCCESS;
}

static char *handle_megaco_set_debug(struct ast_cli_entry *e, int cmd, struct ast_cli_args *a)
{
	switch (cmd) {
	case CLI_INIT:
		e->command = "megaco set debug {on|off}";
		e->usage =
			"Usage: megaco set debug {on|off}\n"
			"       Enables/Disables dumping of Megaco packets for debugging purposes\n";
		return NULL;
	case CLI_GENERATE:
		return NULL;
	}

	if (a->argc != e->args)
		return CLI_SHOWUSAGE;

	if (!strncasecmp(a->argv[e->args - 1], "on", 2)) {
		mgcpdebug = 1;
		ast_cli(a->fd, "Megaco------------------ Debugging Enabled\n");
	} else if (!strncasecmp(a->argv[3], "off", 3)) {
		mgcpdebug = 0;
		ast_cli(a->fd, "MGCP Debugging Disabled\n");
	} else {
		return CLI_SHOWUSAGE;
	}
	return CLI_SUCCESS;
}

static struct ast_cli_entry cli_megaco[] = {
	AST_CLI_DEFINE(handle_megaco_audit_endpoint, "Audit specified MEGACO endpoint"),
	AST_CLI_DEFINE(handle_megaco_show_megacomg, "List defined MEGACO megacomg"),
	AST_CLI_DEFINE(handle_megaco_show_mguser, "List defined MEGACO mguser"),
	AST_CLI_DEFINE(handle_megaco_reset_mguser, "Reset defined MEGACO mguser"),
	AST_CLI_DEFINE(handle_megaco_set_debug, "Enable/Disable MEGACO debugging"),
	AST_CLI_DEFINE(mgcp_reload, "Reload Megaco configuration"),
	AST_CLI_DEFINE(megaco_test, "MEgaco Test "),

};

static int megaco_answer(struct ast_channel *ast)
{
	int res = 0;
	struct megaco_subchannel *sub = ast_channel_tech_pvt(ast);
	struct megaco_users *p = sub->parent;

	return res;
}

static struct ast_frame *mgcp_rtp_read(struct megaco_subchannel *sub)
{
	/* Retrieve audio/etc from channel.  Assumes sub->lock is already held. */
		struct ast_frame *f;

		f = ast_rtp_instance_read(sub->rtp, 0);
		/* Don't send RFC2833 if we're not supposed to */
		if (f && (f->frametype == AST_FRAME_DTMF) && !(sub->parent->dtmfmode & MGCP_DTMF_RFC2833))
			return &ast_null_frame;
		if (sub->owner) {
			/* We already hold the channel lock */
			if (f->frametype == AST_FRAME_VOICE) {
				if (!ast_format_cap_iscompatible(ast_channel_nativeformats(sub->owner), &f->subclass.format)) {
					ast_debug(1, "Oooh, format changed to %s\n", ast_getformatname(&f->subclass.format));
					ast_format_cap_set(ast_channel_nativeformats(sub->owner), &f->subclass.format);
					ast_set_read_format(sub->owner, ast_channel_readformat(sub->owner));
					ast_set_write_format(sub->owner, ast_channel_writeformat(sub->owner));
				}
				/* Courtesy fearnor aka alex@pilosoft.com */
				if ((sub->parent->dtmfmode & MGCP_DTMF_INBAND) && (sub->parent->dsp)) {
	#if 0
					ast_log(LOG_NOTICE, "MGCP ast_dsp_process\n");
	#endif
					f = ast_dsp_process(sub->owner, sub->parent->dsp, f, 0);
				}
			}
		}
		return f;
}


static struct ast_frame *megaco_read(struct ast_channel *ast)
{
	struct ast_frame *f;
	struct megaco_subchannel *sub = ast_channel_tech_pvt(ast);
	ast_mutex_lock(&sub->lock);
	f = mgcp_rtp_read(sub);
	ast_mutex_unlock(&sub->lock);
	return f;
}

static int megaco_write(struct ast_channel *ast, struct ast_frame *frame)
{
	struct megaco_subchannel *sub = ast_channel_tech_pvt(ast);
		int res = 0;
		char buf[256];

		if (frame->frametype != AST_FRAME_VOICE) {
			if (frame->frametype == AST_FRAME_IMAGE)
				return 0;
			else {
				ast_log(LOG_WARNING, "Can't send %u type frames with MGCP write\n", frame->frametype);
				return 0;
			}
		} else {
			if (!(ast_format_cap_iscompatible(ast_channel_nativeformats(ast), &frame->subclass.format))) {
				ast_log(LOG_WARNING, "Asked to transmit frame type %s, while native formats is %s (read/write = %s/%s)\n",
					ast_getformatname(&frame->subclass.format),
					ast_getformatname_multiple(buf, sizeof(buf), ast_channel_nativeformats(ast)),
					ast_getformatname(ast_channel_readformat(ast)),
					ast_getformatname(ast_channel_writeformat(ast)));
				/* return -1; */
			}
		}
		if (sub) {
			ast_mutex_lock(&sub->lock);
			if (!sub->sdpsent && sub->gate) {
				if (sub->gate->state == GATE_ALLOCATED) {
					ast_debug(1, "GATE ALLOCATED, sending sdp\n");
					transmit_modify_with_sdp(sub, NULL, 0);
				}
			}
			if ((sub->parent->sub == sub) || !sub->parent->singlepath) {
				if (sub->rtp) {
					res =  ast_rtp_instance_write(sub->rtp, frame);
				}
			}
			ast_mutex_unlock(&sub->lock);
		}
		return res;
}

static int megaco_fixup(struct ast_channel *oldchan, struct ast_channel *newchan)
{
	struct megaco_subchannel *sub = ast_channel_tech_pvt(newchan);

		ast_mutex_lock(&sub->lock);
		ast_log(LOG_NOTICE, "megaco_fixup(%s, %s)\n", ast_channel_name(oldchan), ast_channel_name(newchan));
		
		if (sub->owner != oldchan) 
		{
			ast_mutex_unlock(&sub->lock);
			ast_log(LOG_WARNING, "old channel wasn't %p but was %p\n", oldchan, sub->owner);
			return -1;
		}
		sub->owner = newchan;
		ast_mutex_unlock(&sub->lock);
		return 0;
}

static int mgcp_senddigit_begin(struct ast_channel *ast, char digit)
{
	struct megaco_subchannel *sub = ast_channel_tech_pvt(ast);
	struct megaco_users *p = sub->parent;
	int res = 0;



	return res;
}

static int mgcp_senddigit_end(struct ast_channel *ast, char digit, unsigned int duration)
{
	struct megaco_subchannel *sub = ast_channel_tech_pvt(ast);
	struct megaco_users *p = sub->parent;
	int res = 0;
	char tmp[4];



	return res;
}

/*!
 *  \brief  megaco_devicestate: channel callback for device status monitoring
 *  \param  data tech/resource name of MGCP device to query
 *
 * Callback for device state management in channel subsystem
 * to obtain device status (up/down) of a specific MGCP endpoint
 *
 *  \return device status result (from devicestate.h) AST_DEVICE_INVALID (not available) or AST_DEVICE_UNKNOWN (available but unknown state)
 */
static int megaco_devicestate(const char *data)
{
	struct megaco_mg  *g;
	struct megaco_users *e = NULL;
	char *tmp, *endpt, *gw;
	int ret = AST_DEVICE_INVALID;


	ret = AST_DEVICE_UNKNOWN;

error:
	ast_mutex_unlock(&gatelock);
	return ret;
}

static char *megacostate2str(int state) {
	switch (state) {
		   case MEGACO_IDLE_ST:
		   			return "MEGACO_IDLE_ST";
		   case MEGACO_WFDIGIT_ST:
		   			return "MEGACO_WFDIGIT_ST";
		   case MEGACO_WFANSWER_ST:
		   			return "EGACO_WFANSWER_ST";
		   case MEGACO_ANSWER_ST:
		   			return "MEGACO_ANSWER_ST";
		   case MEGACO_RING_ST:
		   			return "MEGACO_RING_ST";
	//call state for incomming from sip suers
			case 	MEGACO_SIP_WFANSWER_ST:
					return "MEGACO_SIP_WFANSWER_ST";
			case	MEGACO_SIP_ANSWER_ST:
					return "MEGACO_SIP_ANSWER_ST";
			case	MEGACO_SIP_HOLD_ST:
					return "MEGACO_SIP_HOLD_ST";
	//call from MG to SIP user
			case	MEGACO_MG_WFRINGACK_ST:
					return "MEGACO_MG_WFRINGACK_ST";
			case	MEGACO_MG_WFANSWER_ST:
					return "MEGACO_MG_WFANSWER_ST";
			case	MEGACO_MG_ANSWER_ST:
					return "MEGACO_MG_ANSWER_ST";

			case MEGACO_WFONHOOK_ST:
					return "MEGACO_WFONHOOK_ST";
			case MG_AWAIT_INIT_OK_ST:
					return "MG_AWAIT_INIT_OK_ST";
			case MG_ALLIVE_ST:
					return "MG_ALLIVE_ST";
			case  MG_BROKEN_ST:
					return "MG_BROKEN_ST";
			case MEGACO_CALL_WAITING_ST:
				return  "MEGACO_CALL_WAITING_ST";
			break;

	}
	return "MEGACO-UNKNOWN-ST";
}



static char *control2str(int ind) {
	switch (ind) {
	case AST_CONTROL_HANGUP:
		return "Other end has hungup";
	case AST_CONTROL_RING:
		return "Local ring";
	case AST_CONTROL_RINGING:
		return "Remote end is ringing";
	case AST_CONTROL_ANSWER:
		return "Remote end has answered";
	case AST_CONTROL_BUSY:
		return "Remote end is busy";
	case AST_CONTROL_TAKEOFFHOOK:
		return "Make it go off hook";
	case AST_CONTROL_OFFHOOK:
		return "Line is off hook";
	case AST_CONTROL_CONGESTION:
		return "Congestion (circuits busy)";
	case AST_CONTROL_FLASH:
		return "Flash hook";
	case AST_CONTROL_WINK:
		return "Wink";
	case AST_CONTROL_OPTION:
		return "Set a low-level option";
	case AST_CONTROL_RADIO_KEY:
		return "Key Radio";
	case AST_CONTROL_RADIO_UNKEY:
		return "Un-Key Radio";
	case  AST_CONTROL_HOLD :
					return "Start music on Hold";
    case AST_CONTROL_UNHOLD:
    				return "Stop music on Hold";
	case AST_CONTROL_SRCCHANGE: 
					return  "Media source has changed and requires a new RTP SSRC";
	case AST_CONTROL_SRCUPDATE:
	          return  "Media source Update";
	break;


	}
	return "UNKNOWN";
}

static int megaco_indicate(struct ast_channel *ast, int ind, const void *data, size_t datalen)
{
	struct megaco_subchannel *sub = ast_channel_tech_pvt(ast);
	int res = 0;
	struct sockaddr_in sintest;
	struct sockaddr_in sin;
	struct ast_sockaddr sin_tmp;

	ast_verb(3, "Megaco  asked to indicate %d '%s' condition on channel %s State:%s \n",
		ind, control2str(ind), ast_channel_name(ast),megacostate2str(sub->parent->callstate));
	ast_mutex_lock(&sub->lock);

	switch(ind) {
	case AST_CONTROL_RINGING:
				switch(sub->parent->callstate)
				{
				case MEGACO_MG_WFRINGACK_ST:
					ast_verb(3,"--------------------------AST_CONTROL_RINGING ContexID:%s N:%s State:%s \n",sub->parent->contextId,sub->parent->name,megacostate2str(sub->parent->callstate));
					transmit_ModifyRingBackTone1(sub->parent->contextId,sub->parent->name,sub);
					sub->parent->callstate = MEGACO_MG_WFANSWER_ST;
					break;
				default:
					ast_verb(3,"Invalid  AST_CONTROL_RINGING on<%s> state :%s\n",sub->parent->name,megacostate2str(sub->parent->callstate));
					break;
				}
		break;
	case AST_CONTROL_BUSY:
		ast_verb(3,"--------------------------AST_CONTROL_BUSY  ContexID:%s N:%s State:%s \n",sub->parent->contextId,sub->parent->name,megacostate2str(sub->parent->callstate));
		transmit_ModifyBusyTone(sub->parent->contextId,sub->parent->name,sub);
		sub->parent->callstate = MEGACO_WFONHOOK_ST;
		break;
	case AST_CONTROL_INCOMPLETE:
		/* We do not currently support resetting of the Interdigit Timer, so treat
		 * Incomplete control frames as a congestion response
		 */

	case AST_CONTROL_CONGESTION:
		ast_verb(3,"----------------------------------------AST_CONTROL_CONGESTION \n");
		transmit_ModifyBusyTone(sub->parent->contextId,sub->parent->name,sub);
		break;
	
//comment by mkmtest960420
	case AST_CONTROL_HOLD:
     	ast_verb(3,">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>AST_CONTROL_HOLD : <%s@%s> State:%s\n",sub->parent->name,sub->parent->parent->name,megacostate2str(sub->parent->callstate));
    /*    transmit_ModifyTdmNoSignalWithSDP_2(NULL,sub->parent->contextId,sub->parent->name,sub,NULL); 
		ast_moh_start(ast, data, NULL);
		sub->parent->callstate = MEGACO_CALL_WAITING_ST;*/
		break;
	case AST_CONTROL_UNHOLD:
	    ast_verb(3,">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>AST_CONTROL_UNHOLD : <%s@%s> State:%s\n",sub->parent->name,sub->parent->parent->name,megacostate2str(sub->parent->callstate));
		/*transmit_ModifyTdmNoSignalWithSDP_1(NULL,sub->parent->contextId,sub->parent->name,sub,NULL);
		ast_moh_stop(ast);*/

		break;
//comment by mkmtest960420

	case AST_CONTROL_PROGRESS:
			ast_verb(3,"--------------------------AST_CONTROL_PROGRESS \n");


			ast_rtp_instance_update_source(sub->rtp);
			ast_rtp_instance_get_local_address(sub->rtp, &sin_tmp);
			ast_sockaddr_to_sin(&sin_tmp, &sin);
			ast_verb(3, "We're at %s port %d\n", ast_inet_ntoa(sin.sin_addr), ntohs(sin.sin_port));
			sub->moh_port =  ntohs(sin.sin_port);
			transmit_ModifyPalyCrbt(NULL,sub->parent->contextId,sub->parent->name,sub,NULL);
			sub->parent->callstate =MEGACO_SIP_ANSWER_ST;

			break;
   /* case AST_CONTROL_HOLD:
          ast_verb(3,">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>AST_CONTROL_HOLD : <%s@%s> State:%s\n",sub->parent->name,sub->parent->parent->name,megacostate2str(sub->parent->callstate));
			ast_rtp_instance_update_source(sub->rtp);
			ast_rtp_instance_get_local_address(sub->rtp, &sin_tmp);
			ast_sockaddr_to_sin(&sin_tmp, &sin);
			ast_verb(3, "We're at %s port %d\n", ast_inet_ntoa(sin.sin_addr), ntohs(sin.sin_port));
			ast_sockaddr_to_sin(&sin_tmp, &sub->rtp_remote_sin); // ONJA
			ast_rtp_instance_get_remote_address(sub->rtp, &sin_tmp);
			ast_sockaddr_to_sin(&sin_tmp, &sin);
			ast_verb(3, "remote at %s port %d\n", ast_inet_ntoa(sin.sin_addr), ntohs(sin.sin_port));
			//megaco_get_remote_param(sub->parent->name,&sub->parent->parent->addr);  // INJAST
			transmit_ModifyTdmNoSignalWithSDP_1(NULL,sub->parent->contextId,sub->parent->name,sub,NULL);
			sub->parent->callstate =MEGACO_SIP_ANSWER_ST;
   			 break;*/
	case AST_CONTROL_SRCUPDATE:
		
		/*( sub->parent->callstate == MEGACO_SIP_HOLD_ST)
	    {
			ast_verb(3,">>>>>>>>HOLD>>>>>>>>>>>>>>AST_CONTROL_SRCUPDATE : <%s@%s> State:%s\n",sub->parent->name,sub->parent->parent->name,megacostate2str(sub->parent->callstate));	    	


			ast_rtp_instance_update_source(sub->rtp);
			ast_rtp_instance_get_local_address(sub->rtp, &sin_tmp);
			ast_sockaddr_to_sin(&sin_tmp, &sin);
			ast_verb(3, "We're at %s port %d\n", ast_inet_ntoa(sin.sin_addr), ntohs(sin.sin_port));
			ast_sockaddr_to_sin(&sin_tmp, &sub->rtp_remote_sin); // ONJA
			ast_rtp_instance_get_remote_address(sub->rtp, &sin_tmp);
			ast_sockaddr_to_sin(&sin_tmp, &sin);
			ast_verb(3, "remote at %s port %d\n", ast_inet_ntoa(sin.sin_addr), ntohs(sin.sin_port));
			//megaco_get_remote_param(sub->parent->name,&sub->parent->parent->addr);  // INJAST
			megaco_get_remote_paramfromholdchannel(sub->parent->name,&sub->parent->parent->addr);
			transmit_ModifyTdmNoSignalWithSDP_1(NULL,sub->parent->contextId,sub->parent->name,sub,NULL);
			sub->parent->callstate =MEGACO_SIP_ANSWER_ST;

	    }
	    else{*/
			
			ast_verb(3,">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>AST_CONTROL_SRCUPDATE : <%s@%s> State:%s\n",sub->parent->name,sub->parent->parent->name,megacostate2str(sub->parent->callstate));
            /*if(strstr(sub->parent->name,"A1" )){            	
            sub->parent->callstate =MEGACO_SIP_ANSWER_ST;
            	return;
            }*/
			ast_rtp_instance_update_source(sub->rtp);
			ast_rtp_instance_get_local_address(sub->rtp, &sin_tmp);
			ast_sockaddr_to_sin(&sin_tmp, &sin);
			ast_verb(3, "We're at %s port %d direct_media:%d\n", ast_inet_ntoa(sin.sin_addr), ntohs(sin.sin_port),sub->parent->directmedia);
			ast_sockaddr_to_sin(&sin_tmp, &sub->rtp_remote_sin); // ONJA
			ast_rtp_instance_get_remote_address(sub->rtp, &sin_tmp);
			ast_sockaddr_to_sin(&sin_tmp, &sin);



			if(sub->parent->directmedia )//&& !sub->peyvast)
			{
				struct ast_channel *peer_channel;
				peer_channel = ast_bridged_channel(sub->owner);
				sub->direct_peer = peer_channel;
				char *checks, checkm;
                 checks = strstr(ast_channel_name(peer_channel),"SIP");
				checkm = strstr(ast_channel_name(peer_channel),"MEGACO");
				if( checkm)
			 	{
	                        	struct megaco_subchannel *m_subchannel = ast_channel_tech_pvt(sub->direct_peer);
                        		ast_rtp_instance_get_remote_address(m_subchannel->rtp, &sin_tmp);
                        		ast_sockaddr_to_sin(&sin_tmp, &sub->rtp_remote_sin);
                                	ast_sockaddr_to_sin(&sin_tmp, &sintest);
                                	ast_verb(3, "\n\n\n mohsen: src_update in directmedia at %s port %d\n\n\n", ast_inet_ntoa(sintest.sin_addr), ntohs(sintest.sin_port));
					}
				else if( checks)
			 	{	int doing_directmedia; //= TRUE;
	                        	struct sip_pvt *s_subchannel = ast_channel_tech_pvt(sub->direct_peer);
					if(sub->parent->callwaiting)
				                ast_clear_flag(&s_subchannel->flags[0], SIP_REINVITE);

					if (ast_test_flag(&s_subchannel->flags[0], SIP_REINVITE))
					{ 
						ast_verb(3,"\n\n\n #################################### doing_directmedia: %d  ###################################### \n\n\n",doing_directmedia);
						ast_rtp_instance_get_remote_address(s_subchannel->rtp, &sin_tmp);
                        			ast_sockaddr_to_sin(&sin_tmp, &sub->rtp_remote_sin);
                        			ast_sockaddr_to_sin(&sin_tmp, &sintest);
	                        		ast_verb(3, "\n\n\n mohsen: src_update in directmedia at %s port %d\n\n\n", ast_inet_ntoa(sintest.sin_addr), ntohs(sintest.sin_port));
						}
					}
			} else
				{
				ast_verb(3,"\n\n\n ########################################### directmedia is not enabled or not permitted ################################################ \n\n\n");

				}

			ast_verb(3, "remote at %s port %d\n", ast_inet_ntoa(sin.sin_addr), ntohs(sin.sin_port));
			
			//megaco_get_remote_param(sub->parent->name,&sub->parent->parent->addr);  // INJAST
			transmit_ModifyTdmNoSignalWithSDP_1(NULL,sub->parent->contextId,sub->parent->name,sub,NULL);
			sub->parent->callstate =MEGACO_SIP_ANSWER_ST;

		
		//}


		break;
	case AST_CONTROL_SRCCHANGE:
		ast_verb(3,">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>AST_CONTROL_SRCCHANGE %s@%s With ContxtID:%s \n",sub->parent->name,sub->parent->parent->name,sub->parent->contextId);
		ast_rtp_instance_change_source(sub->rtp);
		break;


	case AST_CONTROL_PROCEEDING:
		transmit_modify_request(sub);
	case -1:
		switch(sub->parent->callstate)
		{
		case MEGACO_MG_WFRINGACK_ST:
			ast_rtp_instance_update_source(sub->rtp);
			ast_rtp_instance_get_local_address(sub->rtp, &sin_tmp);
			ast_sockaddr_to_sin(&sin_tmp, &sin);
			ast_verb(3, "We're at %s port %d\n", ast_inet_ntoa(sin.sin_addr), ntohs(sin.sin_port));
			ast_sockaddr_to_sin(&sin_tmp, &sub->rtp_remote_sin); // ONJA
			ast_rtp_instance_get_remote_address(sub->rtp, &sin_tmp);
			ast_sockaddr_to_sin(&sin_tmp, &sin);
			ast_verb(3, "remote at %s port %d\n", ast_inet_ntoa(sin.sin_addr), ntohs(sin.sin_port));
			//megaco_get_remote_param(sub->parent->name,&sub->parent->parent->addr);  // INJAST
			transmit_ModifyTdmNoSignalWithSDP_1(NULL,sub->parent->contextId,sub->parent->name,sub,NULL);

			sub->parent->callstate =MEGACO_MG_ANSWER_ST;
			break;
		default:
			break;
		}
		break;
	case AST_CONTROL_CONNECTED_LINE:
		switch(sub->parent->callstate)
		{
			case MEGACO_MG_WFRINGACK_ST:
				ast_verb(3,"AST_CONTROL_CONNECTED_LINE::MEGACO_MG_WFRINGACK_ST ring Ack is received: %s\n",sub->parent->name);
				sub->parent->callstate = MEGACO_MG_WFANSWER_ST;
				break;
			case MEGACO_MG_WFANSWER_ST	:
			      ast_verb(3,"AST_CONTROL_CONNECTED_LINE::MEGACO_MG_WFANSWER_ST ring Ack is received: %s\n",sub->parent->name);
				break;
			default:
				ast_verb(3,"AST_CONTROL_CONNECTED_LINE::UNKNOWN ring Ack is received: %s\n",sub->parent->name);
				break;
		}
//		ast_verb(3,"Answer from sip to :%s",sub->parent->name);
		/*transmit_ModifyTdmNoSignalWithSDP(NULL,sub->parent->contextId,sub->parent->name,sub,NULL);
		sub->parent->callstate = MEGACO_MG_ANSWER_ST;*/
		break;

	default:
		ast_log(LOG_WARNING, "Don't know how to indicate condition %d\n", ind);
		/* fallthrough */
	case AST_CONTROL_PVT_CAUSE_CODE:
		res = -1;


	}

	ast_mutex_unlock(&sub->lock);
	return res;
}
//mojtaba
static struct ast_channel *megaco_new(struct megaco_subchannel *sub, int state, const char *linkedid,int mojtaba)
{
	struct ast_channel *tmp;
	struct ast_variable *v = NULL;
	struct megaco_users *i = sub->parent;
	struct ast_format tmpfmt;

	//ast_verb(3,"megaco_new with below item:  cid_num:%s cid_name:%s accountcode:%s exten:%s context:%s  state:%s\n", i->cid_num, i->cid_name, i->accountcode, i->exten, i->context,megacostate2str(sub->parent->callstate));
    if(mojtaba==0)
	//outgoing call
		tmp = ast_channel_alloc(1, state, i->cid_num, i->cid_name, linkedid, i->accountcode, i->exten,i->context, i->amaflags, "MEGACO/%s-m%07x", i->name, (unsigned)ast_atomic_fetchadd_int((int *)&megaco_chan_idx_out, +1));
	else
		tmp = ast_channel_alloc(1, state, i->cid_num, i->cid_name, linkedid, i->accountcode, i->exten,i->context, i->amaflags, "MEGACO/%s-i%07x", i->name, (unsigned)ast_atomic_fetchadd_int((int *)&megaco_chan_idx, +1));		

	if (!tmp) {
		ast_log(LOG_WARNING, "Unable to allocate AST channel structure for Megaco channel\n");
		//sip_pvt_lock(i);
		return NULL;
	}
	ast_mutex_lock(&sub->lock);
	if (tmp) {
		ast_channel_tech_set(tmp, &mgcp_tech);
		ast_format_cap_copy(ast_channel_nativeformats(tmp), i->cap);
		if (ast_format_cap_is_empty(ast_channel_nativeformats(tmp))) {
			ast_format_cap_copy(ast_channel_nativeformats(tmp), global_capability);
		}
		/*if(sub->parent->callstate == MEGACO_SIP_ANSWER_ST)
		{
			if (sub->rtp_hold) {
			ast_verb(3,"rtrtrtrtrtrtrtrtrtrtrtrtrtrtrt\n");
			ast_channel_set_fd(tmp, 0, ast_rtp_instance_fd(sub->rtp_hold, 0));
			}
		}else*/


		if (sub->rtp) {
			ast_channel_set_fd(tmp, 0, ast_rtp_instance_fd(sub->rtp, 0));
		}
		else
		{
			ast_log(LOG_WARNING, " Unable to USE RTP pointer \n");	
		}

		if (i->dtmfmode & (MGCP_DTMF_INBAND | MGCP_DTMF_HYBRID)) {
			i->dsp = ast_dsp_new();
			ast_dsp_set_features(i->dsp, DSP_FEATURE_DIGIT_DETECT);
			/* this is to prevent clipping of dtmf tones during dsp processing */
			ast_dsp_set_digitmode(i->dsp, DSP_DIGITMODE_NOQUELCH);
		} else {
			i->dsp = NULL;
		}
		if (state == AST_STATE_RING)
			ast_channel_rings_set(tmp, 1);

		ast_best_codec(ast_channel_nativeformats(tmp), &tmpfmt);
		ast_format_copy(ast_channel_writeformat(tmp), &tmpfmt);
		ast_format_copy(ast_channel_rawwriteformat(tmp), &tmpfmt);
		ast_format_copy(ast_channel_readformat(tmp), &tmpfmt);
		ast_format_copy(ast_channel_rawreadformat(tmp), &tmpfmt);
		ast_channel_tech_pvt_set(tmp, sub);
		if (!ast_strlen_zero(i->language))
			ast_channel_language_set(tmp, i->language);
		if (!ast_strlen_zero(i->accountcode))
			ast_channel_accountcode_set(tmp, i->accountcode);
		if (i->amaflags)
			ast_channel_amaflags_set(tmp, i->amaflags);

		//comment by mkmtest960420
		/*if(sub->parent->callstate == MEGACO_SIP_ANSWER_ST)
		{
			sub->owner_hold = tmp;
			sub->parent->iscallwaiting =1;
			ast_verb(3,"initialized CalleWaitning \n");
		}
		else*/
		//comment by mkmtest960420
			sub->owner = tmp;

		ast_module_ref(ast_module_info->self);
		ast_channel_callgroup_set(tmp, i->callgroup);
		ast_channel_pickupgroup_set(tmp, i->pickupgroup);
		ast_channel_call_forward_set(tmp, i->call_forward);
		ast_channel_context_set(tmp, i->context);
		ast_channel_exten_set(tmp, i->exten);

		/* Don't use ast_set_callerid() here because it will
		 * generate a needless NewCallerID event */
		if (!ast_strlen_zero(i->cid_num)) {
			ast_channel_caller(tmp)->ani.number.valid = 1;
			ast_channel_caller(tmp)->ani.number.str = ast_strdup(i->cid_num);
		}

		if (!i->adsi) {
			ast_channel_adsicpe_set(tmp, AST_ADSI_UNAVAILABLE);
		}
		ast_channel_priority_set(tmp, 1);

		/* Set channel variables for this call from configuration */
		for (v = i->chanvars ; v ; v = v->next) {
			char valuebuf[1024];
			pbx_builtin_setvar_helper(tmp, v->name, ast_get_encoded_str(v->value, valuebuf, sizeof(valuebuf)));
		}

		if (sub->rtp) {
			ast_jb_configure(tmp, &global_jbconf);
		}
		if (state != AST_STATE_DOWN) {
			if (ast_pbx_start(tmp)) {
				ast_log(LOG_WARNING, "Unable to start PBX on %s\n", ast_channel_name(tmp));
				ast_hangup(tmp);
				tmp = NULL;
			}
		}
		ast_verb(3, "MEGACO megaco_new(%s) created in state: %s\n",
				ast_channel_name(tmp), ast_state2str(state));
	} else {
		ast_log(LOG_WARNING, "Unable to allocate channel structure\n");
	}
	ast_mutex_unlock(&sub->lock);
	return tmp;
}

static char *get_sdp_by_line(char* line, char *name, int nameLen)
{
	if (strncasecmp(line, name, nameLen) == 0 && line[nameLen] == '=') {
		char *r = line + nameLen + 1;
		while (*r && (*r < 33)) ++r;
		return r;
	}
	return "";
}

static char *get_sdp(struct megaco_request *req, char *name)
{
	int x;
	int len = strlen(name);
	char *r;

	for (x = 0; x < req->lines; x++) {
		r = get_sdp_by_line(req->line[x], name, len);
		if (r[0] != '\0') return r;
	}
	return "";
}

static void sdpLineNum_iterator_init(int *iterator)
{
	*iterator = 0;
}

static char *get_sdp_iterate(int* iterator, struct megaco_request *req, char *name)
{
	int len = strlen(name);
	char *r;
	while (*iterator < req->lines) {
		r = get_sdp_by_line(req->line[(*iterator)++], name, len);
		if (r[0] != '\0') return r;
	}
	return "";
}

static char *__get_header(struct megaco_request *req, char *name, int *start, char *def)
{
	int x;
	int len = strlen(name);
	char *r;
	for (x = *start; x < req->headers; x++) {
		if (!strncasecmp(req->header[x], name, len) &&
		    (req->header[x][len] == ':')) {
			r = req->header[x] + len + 1;
			while (*r && (*r < 33)) {
				r++;
			}
			*start = x + 1;
			return r;
		}
	}
	/* Don't return NULL, so get_header is always a valid pointer */
	return def;
}

static char *get_header(struct megaco_request *req, char *name)
{
	int start = 0;
	return __get_header(req, name, &start, "");
}

/*! \brief get_csv: (SC:) get comma separated value */
static char *get_csv(char *c, int *len, char **next)
{
	char *s;

	*next = NULL, *len = 0;
	if (!c) return NULL;

	while (*c && (*c < 33 || *c == ',')) {
		c++;
	}

	s = c;
	while (*c && (*c >= 33 && *c != ',')) {
		c++, (*len)++;
	}
	*next = c;

	if (*len == 0) {
		s = NULL, *next = NULL;
	}

	return s;
}

static struct megaco_mg *find_realtime_gw(char *name, char *at, struct sockaddr_in *sin)
{
	struct megaco_mg *g = NULL;

	struct ast_variable *mgcpgwconfig = NULL;
	struct ast_variable *gwv, *epname = NULL;
	struct megaco_users *e;
	char lines[256];
	int i, j;

	ast_verb(3, "*** find Realtime MEGACOUSERS\n");

	if (!(i = ast_check_realtime("mgcpgw")) || !(j = ast_check_realtime("mgcpep"))) {
		//ast_verb(3,"dddddddddddddd\n");
		return NULL;
	}

	if (ast_strlen_zero(at)) {
		ast_verb(3, "null gw name\n");
		return NULL;
	}

	if (!(mgcpgwconfig = ast_load_realtime("mgcpgw", "name", at, NULL))) {
		ast_verb(3,"ffffffffffff\n");
		return NULL;
	}


	/*!
	 * \note This is a fairly odd way of instantiating lines.  Instead of each
	 * line created by virtue of being in the database (and loaded via
	 * ast_load_realtime_multientry), this code forces a specific order with a
	 * "lines" entry in the "mgcpgw" record.  This has benefits, because as with
	 * chan_dahdi, values are inherited across definitions.  The downside is
	 * that it's not as clear what the values will be simply by looking at a
	 * single row in the database, and it's probable that the sanest configuration
	 * should have the first column in the "mgcpep" table be "clearvars", with a
	 * static value of "all", if any variables are set at all.  It may be worth
	 * making this assumption explicit in the code in the future, and then just
	 * using ast_load_realtime_multientry for the "mgcpep" records.
	 */
	lines[0] = '\0';
	for (gwv = mgcpgwconfig; gwv; gwv = gwv->next) {
		if (!strcasecmp(gwv->name, "lines")) {
			ast_copy_string(lines, gwv->value, sizeof(lines));
			break;
		}
	}
	/* Position gwv at the end of the list */
	for (gwv = gwv && gwv->next ? gwv : mgcpgwconfig; gwv->next; gwv = gwv->next);

	if (!ast_strlen_zero(lines)) {
		AST_DECLARE_APP_ARGS(args,
			AST_APP_ARG(line)[100];
		);
		AST_STANDARD_APP_ARGS(args, lines);
		for (i = 0; i < args.argc; i++) {
			gwv->next = ast_load_realtime("mgcpep", "name", at, "line", args.line[i], NULL);

			/* Remove "line" AND position gwv at the end of the list. */
			for (epname = NULL; gwv->next; gwv = gwv->next) {
				if (!strcasecmp(gwv->next->name, "line")) {
					/* Remove it from the list */
					epname = gwv->next;
					gwv->next = gwv->next->next;
				}
			}
			/* Since "line" instantiates the configuration, we have to move it to the end. */
			if (epname) {
				gwv->next = epname;
				epname->next = NULL;
				gwv = gwv->next;
			}
		}
	}
	for (gwv = mgcpgwconfig; gwv; gwv = gwv->next) {
		ast_debug(1, "MGCP Realtime var: %s => %s\n", gwv->name, gwv->value);
	}

	if (mgcpgwconfig) {
		g = build_gateway(at, mgcpgwconfig);
		ast_variables_destroy(mgcpgwconfig);
	}
	if (g) {
		g->next = megacomg;
		g->realtime = 1;
		megacomg = g;
		for (e = g->endpoints; e; e = e->next) {
			transmit_audit_endpoint(e);
			e->needaudit = 0;
		}
	}
	return g;
}
static int reset_mg_user_call_state(char *name)
{

	struct megaco_mg *g;
	char *tmpcp,*mgname;
	char temp[128];
 	char mg_name[128];
	int state=0;
	
	struct megaco_users *p = NULL;
	memset(temp,0,sizeof(temp));
	mgname = strcasestr(name,"@");
    if(mgname)
    {
    	strncpy(temp,name,(strlen(name)-strlen(mgname)));
    	mgname= mgname+1;
    }
    else
    {
    	return -1;
    }
	for (g = megacomg ;g;g = g->next)
	{
		tmpcp = strcasestr(mgname,g->name);
		if(tmpcp)
		{
			for (p = g->endpoints; p; p = p->next)
			{
				tmpcp = strcasestr(temp,p->name);
				if(tmpcp)
				{
				  	 memset(name,0,16);
					 memcpy(name,p->name,sizeof(name));
                     state = p->callstate;
                     transmit_ModifyOneSubChannel("-",name,p->sub);
                    // transmit_MgAuditRoot(p->sub);  
                     p->callstate = MEGACO_IDLE_ST;
					 return state;
				}
			}


	    }
	}
	
	return (-1);
}

static int find_mg_user_call_state(char *name)
{

//#ifdef MEGACO_AFCG_METHOD
	struct megaco_mg *g;
	char *tmpcp,*mgname;
	char temp[128];
 	char mg_name[128];
	int postdgt=0;
	
	struct megaco_users *p = NULL;
	memset(temp,0,sizeof(temp));
	mgname = strcasestr(name,"@");
    if(mgname)
    {
    	strncpy(temp,name,(strlen(name)-strlen(mgname)));

    	mgname= mgname+1;
    }
    else
    {
  //  	ast_verb(3,"erooooooooooooooooooor \n");
    	return -1;
    }
	for (g = megacomg ;g;g = g->next)
	{
		tmpcp = strcasestr(mgname,g->name);
		if(tmpcp)
		{
			for (p = g->endpoints; p; p = p->next)
			{
				tmpcp = strcasecmp(temp,p->name);
				if(!tmpcp)
				{

				  	 memset(name,0,16);
					 memcpy(name,p->name,sizeof(name));

					 ast_verb(3,"find_mg_user_call_state mg  %s --  %s will be :%s------%s-----------\n",g->name,ast_inet_ntoa(g->addr.sin_addr),name,p->name);
					 return p->callstate;
				}
			}


	    }
	}
	//ast_verb(3,"sub channel not find :%s @ %s \n",temp ,mgname );
	return (-1);
}
static int sip_find_mg_dest(char *name,struct sockaddr_in *sin)
{


	struct megaco_mg *g;
	char *tmpcp,*mgname;
	char temp[128];
 	char mg_name[128];
	int postdgt=0;
	struct sockaddr_in tempsin;
	struct megaco_users *p = NULL;
	memset(temp,0,sizeof(temp));
	mgname = strcasestr(name,"@");

	ast_log(LOG_WARNING,"Sip_find_mg_dest will be on :%s -- %s  %d, %d \n",temp,mgname,strlen(name),strlen(mgname));
    
    if(mgname)
    {
    	strncpy(temp,name,(strlen(name)-strlen(mgname)));

    	mgname= mgname+1;
    	
    }
    else
    {
    	ast_log(LOG_WARNING,"sip_find_mg_dest Error1 \n");
    	return -1;
    }

	for (g = megacomg ;g;g = g->next)
	{
		tmpcp = strcasestr(mgname,g->name);
		if(tmpcp)
		{
			for (p = g->endpoints; p; p = p->next)
			{
				//ast_verb(3,"mkm Look for %s  s: %s\n" ,p->name , temp );

				tmpcp = strcasecmp(temp,p->name);
				if(!tmpcp)
				{

				  	 memset(name,0,16);
					 memcpy(sin, &g->addr, sizeof(tempsin));
					 memcpy(name,p->name,sizeof(name));

					// ast_verb(3,"sip_find_mg_dest mg  %s --  %s will be :%s------%s-----------\n",g->name,ast_inet_ntoa(g->addr.sin_addr),name,p->name);
					 return 1;
				}
			}


	    }
	}
	ast_verb(3,"sub channel not find :%s @ %s \n",temp ,mgname );
	return 0;
}

static int digit_analyze(struct megaco_request *req,struct megaco_subchannel *sub)
{


	struct megaco_mg *g;
	char tmp[256] = "",*tmpcp;
	char ddd[128];
	int len;
	snprintf(ddd,sizeof(ddd),"%s",ast_inet_ntoa(req->sin.sin_addr));
	ast_copy_string(tmp, req->destId, sizeof(tmp));
	ast_log(LOG_WARNING,"Digit Analyze will be on :%s \n",tmp);
	
	if(strstr(tmp,"T")){
		ast_log(LOG_WARNING,"MEGACO_INVALID_CALL_TYPE :%s\n",sub->parent->name);
		return MEGACO_INVALID_CALL_TYPE;
	}
/*
	if(strlen(tmp)<6){
		ast_log(LOG_WARNING,"MEGACO_INVALID_CALL_TYPE :%s\n",sub->parent->name);
		return MEGACO_INVALID_CALL_TYPE;
	}*/

  return MEGACO_NATIONAL_CALL_TYPE;

#ifdef MKMNOTNEEDED
	for (g = megacomg ;g;g = g->next)
	{

		ast_verb(3,"g->predgt:%s len :%d\n",g->predgt,strlen(g->predgt));
		if(strstr(tmp,g->predgt) && strlen(g->predgt))
		{

			//ast_verb(3,"find predgt on :<%s> lo????????//ok in: <%s >\n",ast_inet_ntoa(g->addr.sin_addr) ,ddd);

			if(!strcmp(ast_inet_ntoa(g->addr.sin_addr) ,ddd))
			{

		        len=strlen(g->predgt);
		        tmpcp = strcasestr(tmp,g->predgt);
		        if(tmpcp)
		        {
		        	 memset(req->destId,0,sizeof(req->destId));
				     strncpy(req->destId,(tmpcp+len-1),(strlen(tmpcp)-len+1));
				     req->destId[0] = 'A';
				     memcpy(&sub->parent->destIp_addr, &g->addr, sizeof(sub->parent->destIp_addr));
				     ast_verb(3,"call type is Local %s %s >> %s@ %s\n",sub->parent->parent->name,g->name,req->destId,ast_inet_ntoa(sub->parent->destIp_addr.sin_addr));
		        }


				return MEGACO_LOCAL_CALL_TYPE;
			}
			else
			{
		        len=strlen(g->predgt);
		        tmpcp = strcasestr(tmp,g->predgt);
		        if(tmpcp)
		        {
		        	 memset(req->destId,0,sizeof(req->destId));
				     strncpy(req->destId,(tmpcp+len-1),(strlen(tmpcp)-len+1));
				     req->destId[0] = 'A';

				     memcpy(&sub->parent->destIp_addr, &g->addr, sizeof(sub->parent->destIp_addr));
				     ast_verb(3,"call type is External %s %s >> %s@ %s\n",sub->parent->parent->name,g->name,req->destId,ast_inet_ntoa(sub->parent->destIp_addr.sin_addr));
		        }

				return MEGACO_EXTERNAL_CALL_TYPE;
			}

			break;
		}
	}

	return MEGACO_NATIONAL_CALL_TYPE;// MEGACO_INVALID_CALL_TYPE;
#endif

}

static struct megaco_subchannel *find_subchannel_and_lock(char *name, int msgid, struct sockaddr_in *sin)
{
	struct megaco_users *p = NULL;
	struct megaco_subchannel *sub = NULL;
	struct megaco_mg *g;
	char tmp[256] = "";
	char *at = NULL, *c;
	int found = 0;
//#ifdef DEBUG_MEGACO_EN
	char destIp[128];

	snprintf(destIp,sizeof(destIp),"%s",ast_inet_ntoa(sin->sin_addr));
	if (mgcpdebug)
		ast_verb(3,"---------------find_subchannel_and_lock %s  from : %s----------------------------\n ",name,destIp);
//#endif
#ifdef NEW_FIND_SUBCHANNLE
	ast_copy_string(tmp, name, sizeof(tmp));
	for (g = megacomg ;g;g = g->next){
		for (p = g->endpoints; p; p = p->next) {
		//	ast_verb(3,"Searching on :%s@%s  <%s> %d\n",p->name,g->name,tmp,strcasecmp(p->name, tmp));
			if((!strcmp(destIp,ast_inet_ntoa( p->parent->addr.sin_addr))&& !strcasecmp(p->name, tmp)))
			{
				//ast_verb(3,"--OK ---------------find %s at %s in %s :%s \n",p->name,g->domain,g->name,ast_inet_ntoa(g->addr.sin_addr));
				sub = p->sub;
				found = 1;
				break;
			}

		}
	}

   if(!found)
	   ast_verb(3,"Megaco subchannle not found :%s \n", name);


#else
	if (name) {
			ast_copy_string(tmp, name, sizeof(tmp));
			at = strchr(tmp, '@');
			if (!at) {
				ast_verb(3, "MGuser '%s' has no at sign!\n", name);
				return NULL;
			}
			*at++ = '\ 0';
		}
		ast_mutex_lock(&gatelock);
		if (at && (at[0] == '[')) {
			at++;
			c = strrchr(at, ']');
			if (c) {
				*c = '\0';
			}
		}



		for (g = megacomg ? megacomg : find_realtime_gw(name, at, sin); g; g = g->next ? g->next : find_realtime_gw(name, at, sin)) {
				if ((!name || !strcasecmp(g->name, at)) &&
				    (sin || g->addr.sin_addr.s_addr || g->defaddr.sin_addr.s_addr)) {
					/* Found the gateway.  If it's dynamic, save it's address -- now for the endpoint */
					if (sin && g->dynamic && name) {
						if ((g->addr.sin_addr.s_addr != sin->sin_addr.s_addr) ||
							(g->addr.sin_port != sin->sin_port)) {
							memcpy(&g->addr, sin, sizeof(g->addr));
							{
								struct ast_sockaddr tmp1, tmp2;
								struct sockaddr_in tmp3 = {0,};

								tmp3.sin_addr = g->ourip;
								ast_sockaddr_from_sin(&tmp1, &g->addr);
								ast_sockaddr_from_sin(&tmp2, &tmp3);
								if (ast_ouraddrfor(&tmp1, &tmp2)) {
									memcpy(&g->ourip, &__ourip, sizeof(g->ourip));
								}
								ast_sockaddr_to_sin(&tmp2, &tmp3);
								g->ourip = tmp3.sin_addr;
							}
							ast_verb(3, "Registered MG users '%s' at %s port %d\n", g->name, ast_inet_ntoa(g->addr.sin_addr), ntohs(g->addr.sin_port));
						}
					/* not dynamic, check if the name matches */
					} else if (name) {
						if (strcasecmp(g->name, at)) {
							continue;
						}
					/* not dynamic, no name, check if the addr matches */
					} else if (!name && sin) {
						if ((g->addr.sin_addr.s_addr != sin->sin_addr.s_addr) ||
						    (g->addr.sin_port != sin->sin_port)) {
							continue;
						}
					} else {
						continue;
					}
					for (p = g->endpoints; p; p = p->next) {
#ifdef DEBUG_MEGACO_EN
						ast_verb(3, "Searching on %s@%s for subchannel\n", p->name, g->name);
#endif
						if (msgid) {
							sub = p->sub;
							found = 1;
							break;
						} else if (name && !strcasecmp(p->name, tmp))
						{
							    ast_verb(3, "find subchannel, assuming current master %s@%s-%d\n",
								p->name, g->name, p->sub->id);
							sub = p->sub;
							found = 1;
							break;
						}
					}
					if (sub && found) {
						ast_mutex_lock(&sub->lock);
						break;
					}
				}
			}
			ast_mutex_unlock(&gatelock);
			if (!sub) {
				if (name) {
					if (g) {
						ast_log(LOG_NOTICE, "Endpoint '%s' not found on gateway '%s'\n", tmp, at);
					} else {
						ast_log(LOG_NOTICE, "Gateway '%s' (and thus its endpoint '%s') does not exist\n", at, tmp);
					}
				}
			}
#endif

			return sub;
}

#define MG_FIBERHOME_TYPE	    0
#define MG_HUAWEI_TYPE       	1
#define MG_KEYMILE_TYPE   		2
#define MG_ZTE_TYPE   			3

static void megaco_parse(struct megaco_request *req,int mg_type)
{
	/* Divide fields by NULL's */
	char *c;
	int f = 0,digitlen;
	int pos = 0 ;
	char *tmpcp,*tmpcp1,digittmp[32];
	c = req->data;


	req->cmd = MEGACO_UNKNOWNCMD;
	while (*c && *c < 33) c++;
	
	switch(mg_type){
		case MG_FIBERHOME_TYPE:	
			tmpcp = strstr(c,"T="); //khorasan jonobi fiber home
	
			if(tmpcp)
			{
				tmpcp = strstr(c,"T=");
				tmpcp1 = strcasestr(c,"{");
				strncpy(req->transactionIDtext,tmpcp+2,(strlen(tmpcp)-strlen(tmpcp1)-2));

				req->transactionFlag = 1 ;
				c = tmpcp1+1;
				//find context ID
				tmpcp = strstr(c,"C=");
				if(tmpcp)
				{
					tmpcp1 = strstr(c,"{");
					strncpy(req->contextId,tmpcp+2,(strlen(tmpcp)-strlen(tmpcp1)-2));
					//ast_verb(3,"Transaction<%s>\n  Context<%s>\n ",req->transactionIDtext,req->contextId);
					c = tmpcp1+1;
				}

				//find command
				tmpcp = strcasestr(c,"SC=");
				if(tmpcp)
				{  //we receive Service cahnge command
					tmpcp1 = strstr(c,"{");
					strncpy(req->servicechangeId,tmpcp+3,(strlen(tmpcp)-strlen(tmpcp1)-3));
					//ast_verb(3,"ServiceChange  <%s> ",req->servicechangeId);
					req->cmd = 	MEGACO_SERVICECHANGE;
					c = tmpcp1+1;
					tmpcp = strcasestr(c,"K{");
				/*	if(tmpcp)
					{
						tmpcp1 = strstr(c,"}");
						ast_verb(3,">>>>>>>>>>>>>>>>> %d %d \n",strlen(tmpcp),strlen(tmpcp1));
						strncpy(req->kvalueId,tmpcp+2,4);
						ast_verb(3,"***********************kvalueId ***************************  <%s> \n",req->kvalueId);
						req->cmd = 	MEGACO_SERVICECHANGE_WITHK;

					}
		*/
					return;
				}
				//find Notify command
				tmpcp = strcasestr(c,"N=");
				if(tmpcp)
				{
						tmpcp1 = strstr(c,"{");
					strncpy(req->notifyId,tmpcp+2,(strlen(tmpcp)-strlen(tmpcp1)-2));
					//ast_verb(3,"NOTIFY  <%s> ",req->notifyId);
					req->cmd = 	MEGACO_NOTIFY;
					c = tmpcp1+1;

					tmpcp = strcasestr(c,"OE=");
					if(tmpcp)
					{
						tmpcp1 = strstr(c,"{");
						strncpy(req->observedEventsId,tmpcp+3,(strlen(tmpcp)-strlen(tmpcp1)-3));
						//ast_verb(3,"ObservedEvents ***************************  %s/ \n",req->observedEventsId);
						c = tmpcp1+1;
						req->al_event = MEGACO_UNKNOWNEVENT;

						tmpcp = strcasestr(c,"al/of");
						if(tmpcp)
						{
							req->al_event = MEGACO_OFFHOOK_EV;
							return;
						}
						tmpcp = strcasestr(c,"al/on");
						if(tmpcp)
						{
							req->al_event = MEGACO_ONHOOK_EV;
							return;
						}
						tmpcp = strcasestr(c,"al/fl");
						if(tmpcp)
						{
							req->al_event = MEGACO_FLASHDETECT_EV;
							ast_verb(3, "mkm Flash detect \n");
							return;
						}
						tmpcp = strcasestr(c,"it/ito");
						if(tmpcp)
						{
							req->al_event = MEGACO_ALLIVECHECK_EV;
							return;
						}

						tmpcp = strcasestr(c,"dd/ce{ds=");
						//find dest digit
						if(tmpcp)
						{
							tmpcp1 = strcasestr(c,",meth");//ommit 33926 form first and add Afor anlaog line
							digitlen = strlen(tmpcp)-strlen(tmpcp1)-11;

		#ifdef NEW_DIGIT_ANALYZE
							strncpy(req->destId,tmpcp+10,digitlen);
							for(f=0;f<digitlen;f++)
							{
								//ast_verb(3,"karimi iiiiiiii digitlen:%d destId:%c \n",digitlen,req->destId[f]);
								if(req->destId[f] == 'E')
									req->destId[f] = '*';
								if(req->destId[f] == 'F')
									req->destId[f] = '#';

							}
		#else
							memset(digittmp,0,sizeof(digittmp));
							strncpy(digittmp,tmpcp+10,digitlen);
							//ast_verb(3,"Digit :<%s> %d %d ",digittmp,strlen(tmpcp),strlen(tmpcp1));
							tmpcp1 = strcasestr(digittmp,"33926");
							if(tmpcp1)
							{

								strncpy(req->destId,digittmp+4,4);
								req->destId[0]='A';
							}
							else
							{
								strncpy(req->destId,digittmp,strlen(digittmp));
							}
		#endif
							ast_log(LOG_WARNING,"Dest_dialdigit <%s>*********>  <%s>\n",req->notifyId,req->destId);
							c = tmpcp1+1;
							req->al_event =MEGACO_DIALDIGIT_EV;
							return;

						}

					return;
					}
				}


			}
			else
			{//
				//reply command 
				tmpcp = strstr(c,"P=");  
				if(tmpcp)
				{
					tmpcp1 = strcasestr(c,"{");
					strncpy(req->replyId,tmpcp+2,(strlen(tmpcp)-strlen(tmpcp1)-2));

					req->transactionFlag = 0 ;
					c = tmpcp1+1;
					//find context ID
					tmpcp = strstr(c,"C=");

					if(tmpcp)
					{
						tmpcp1 = strcasestr(c,"{");
						strncpy(req->contextId,tmpcp+2,(strlen(tmpcp)-strlen(tmpcp1)-2));
						c = tmpcp1+1;

						//find Reply command ID
						tmpcp = strcasestr(c,"MF=");
						if(tmpcp)
						{
							tmpcp1 = strstr(c,"}");
							if(tmpcp1)
							{
								strncpy(req->notifyId,tmpcp+3,(strlen(tmpcp)-strlen(tmpcp1)-3));
								ast_verb(3,"Reply Modify receive %s \n",req->notifyId);
							}
							req->cmd = 	MEGACO_MODIFY;
							return;
						}
						//find Reply command ID
						tmpcp = strcasestr(c,"ER=");
						if(tmpcp)
						{
							tmpcp1 = strstr(c,"{");
							//strncpy(req->errorId,tmpcp+3,(strlen(tmpcp)-strlen(tmpcp1)-3));
							ast_verb(3,"Reply wirh Error ***************************  <%s> %d %d  \n",req->errorId,strlen(tmpcp),strlen(tmpcp1));
							req->cmd = 	MEGACO_ERROR;
							c = tmpcp1+1;
							//must chack latter for more detail such as command reply,......

							return;
						}

						tmpcp = strcasestr(c,"A=");
						if(tmpcp)
						{
							tmpcp1 = strcasestr(c,",A=");
							strncpy(req->notifyId,tmpcp+2,(strlen(tmpcp)-strlen(tmpcp1)-2));
							c = tmpcp1+1;
							tmpcp = strcasestr(c,"A=");
							if(tmpcp)
							{
								tmpcp1 = strcasestr(c,"{M{O");

								if(!tmpcp1)
									tmpcp1 = strcasestr(c,"{M{st=1{L");

								if(!tmpcp1)
								   tmpcp1 = strcasestr(c,"{M{L");

								if(tmpcp1)
								{
									strncpy(req->ephermalId,tmpcp+2,(strlen(tmpcp)-strlen(tmpcp1)-2));
								}
								else
								{
									ast_verb(3,"**hhh****** Add reply Error parse %s  tmpcp1:%s \n",c,tmpcp1);
									return;
								}

							}
							c = tmpcp1+1;

							//initialize to rtp l param
							c= strcasestr(c,"L");
							//ast_verb(3,"\nLLLLLLLLLLL %s %d \n",c,strlen(c));
							tmpcp = strcasestr(c,"L{");
							//ast_verb(3,"??????? %s %d \n",tmpcp,strlen(tmpcp));
							if(tmpcp)
							{
								tmpcp1 = strstr(c,"}");
								//ast_verb(3,"???????:::: %s %d \n",tmpcp1,strlen(tmpcp1));
								strncpy(req->rtpLparam,tmpcp+2,(strlen(tmpcp)-strlen(tmpcp1)-2));
							}

							ast_verb(3,"Add <%s>:Ephermal:<%s>\n",req->notifyId,req->ephermalId);
							/* Now we process any mime content */
							f = 0;
							req->line[f] = req->rtpLparam;
							//ast_verb(3,"------ parse up SDP line param -------\n<%s>\n",req->line[f]);
							for (; *c; c++) {
									if (*c == '\n') {
										/* We've got a new line */
										*c = 0;
										//ast_verb(3, "Line: %s (%d)\n", req->line[f], (int) strlen(req->line[f]));
										if (f >= MGCP_MAX_LINES - 1) {
											ast_log(LOG_WARNING, "Too many SDP lines...\n");
										} else {
											f++;
										}
										req->line[f] = c + 1;
									} else if (*c == '\r') {
										/* Ignore and eliminate \r's */
										*c = 0;
									}
								}
								/* Check for last line */
								if (!ast_strlen_zero(req->line[f])) {
									f++;
								}
								req->lines = f;

								/*if(req->lines==6)
								{
									req->lines =5;
									req->line[5]='\0';
								}*/




							req->cmd = 	MEGACO_ADD;
							//c = tmpcp1+1;

							return;
						}
						
						tmpcp = strcasestr(c,"s=");
						if(tmpcp)
						{
							ast_verb(3, "------------------Subtract Command\n");
							req->cmd =MEGACO_SUBTRACT;
							return;
						}
						tmpcp = strcasestr(c,"av=");
						if(tmpcp)
						{
							tmpcp1 = strstr(c,"}");
							if(tmpcp1)
							{
								strncpy(req->notifyId,tmpcp+3,(strlen(tmpcp)-strlen(tmpcp1)-3));
								ast_verb(3,"Reply Audit receive %s \n",req->notifyId);
							}
							req->cmd =MEGACO_AUDIT;
							ast_verb(3, "-----------------------------Audit Reply\n");
							return;
						}
					}



				}
				else
				{
					//unhandled megaco message
					req->transactionFlag = 2;
					ast_log(LOG_WARNING, "megaco command Errror %s \n", c);
					ast_verb(3, "megaco command Errror %s \n", c);
				}

			}
	break;
	
	case MG_HUAWEI_TYPE:
	case MG_KEYMILE_TYPE:
	default:
	
			tmpcp = strstr(c," T=");   //keymile huawei
			if(tmpcp)
			{
				tmpcp = strstr(c,"T=");
				tmpcp1 = strcasestr(c,"{");
				strncpy(req->transactionIDtext,tmpcp+2,(strlen(tmpcp)-strlen(tmpcp1)-2));

				req->transactionFlag = 1 ;
				c = tmpcp1+1;
				//find context ID
				tmpcp = strstr(c,"C=");
				if(tmpcp)
				{
					tmpcp1 = strstr(c,"{");
					strncpy(req->contextId,tmpcp+2,(strlen(tmpcp)-strlen(tmpcp1)-2));
					//ast_verb(3,"Transaction<%s>\n  Context<%s>\n ",req->transactionIDtext,req->contextId);
					c = tmpcp1+1;
				}

				//find command
				tmpcp = strcasestr(c,"SC=");
				if(tmpcp)
				{  //we receive Service cahnge command
					tmpcp1 = strstr(c,"{");
					strncpy(req->servicechangeId,tmpcp+3,(strlen(tmpcp)-strlen(tmpcp1)-3));
					//ast_verb(3,"ServiceChange  <%s> ",req->servicechangeId);
					req->cmd = 	MEGACO_SERVICECHANGE;
					c = tmpcp1+1;
					tmpcp = strcasestr(c,"K{");
				/*	if(tmpcp)
					{
						tmpcp1 = strstr(c,"}");
						ast_verb(3,">>>>>>>>>>>>>>>>> %d %d \n",strlen(tmpcp),strlen(tmpcp1));
						strncpy(req->kvalueId,tmpcp+2,4);
						ast_verb(3,"***********************kvalueId ***************************  <%s> \n",req->kvalueId);
						req->cmd = 	MEGACO_SERVICECHANGE_WITHK;

					}
		*/
					return;
				}
				//find Notify command
				tmpcp = strcasestr(c,"N=");
				if(tmpcp)
				{
						tmpcp1 = strstr(c,"{");
					strncpy(req->notifyId,tmpcp+2,(strlen(tmpcp)-strlen(tmpcp1)-2));
					//ast_verb(3,"NOTIFY  <%s> ",req->notifyId);
					req->cmd = 	MEGACO_NOTIFY;
					c = tmpcp1+1;

					tmpcp = strcasestr(c,"OE=");
					if(tmpcp)
					{
						tmpcp1 = strstr(c,"{");
						strncpy(req->observedEventsId,tmpcp+3,(strlen(tmpcp)-strlen(tmpcp1)-3));
						//ast_verb(3,"ObservedEvents ***************************  %s/ \n",req->observedEventsId);
						c = tmpcp1+1;
						req->al_event = MEGACO_UNKNOWNEVENT;

						tmpcp = strcasestr(c,"al/of");
						if(tmpcp)
						{
							req->al_event = MEGACO_OFFHOOK_EV;
							return;
						}
						tmpcp = strcasestr(c,"al/on");
						if(tmpcp)
						{
							req->al_event = MEGACO_ONHOOK_EV;
							return;
						}
						tmpcp = strcasestr(c,"al/fl");
						if(tmpcp)
						{
							req->al_event = MEGACO_FLASHDETECT_EV;
							ast_verb(3, "mkm Flash detect \n");
							return;
						}
						tmpcp = strcasestr(c,"it/ito");
						if(tmpcp)
						{
							req->al_event = MEGACO_ALLIVECHECK_EV;
							return;
						}

						tmpcp = strcasestr(c,"dd/ce{ds=");
						//find dest digit
						if(tmpcp)
						{
							tmpcp1 = strcasestr(c,",meth");//ommit 33926 form first and add Afor anlaog line
							digitlen = strlen(tmpcp)-strlen(tmpcp1)-11;

		#ifdef NEW_DIGIT_ANALYZE
							strncpy(req->destId,tmpcp+10,digitlen);
							for(f=0;f<digitlen;f++)
							{
								//ast_verb(3,"karimi iiiiiiii digitlen:%d destId:%c \n",digitlen,req->destId[f]);
								if(req->destId[f] == 'E')
									req->destId[f] = '*';
								if(req->destId[f] == 'F')
									req->destId[f] = '#';

							}
		#else
							memset(digittmp,0,sizeof(digittmp));
							strncpy(digittmp,tmpcp+10,digitlen);
							//ast_verb(3,"Digit :<%s> %d %d ",digittmp,strlen(tmpcp),strlen(tmpcp1));
							tmpcp1 = strcasestr(digittmp,"33926");
							if(tmpcp1)
							{

								strncpy(req->destId,digittmp+4,4);
								req->destId[0]='A';
							}
							else
							{
								strncpy(req->destId,digittmp,strlen(digittmp));
							}
		#endif
							ast_log(LOG_WARNING,"Dest_dialdigit <%s>*********>  <%s>\n",req->notifyId,req->destId);
							c = tmpcp1+1;
							req->al_event =MEGACO_DIALDIGIT_EV;
							return;

						}

					return;
					}
				}


			}
			else
			{//
				//reply command 
				tmpcp = strstr(c,"P=");  
				if(tmpcp)
				{
					tmpcp1 = strcasestr(c,"{");
					strncpy(req->replyId,tmpcp+2,(strlen(tmpcp)-strlen(tmpcp1)-2));

					req->transactionFlag = 0 ;
					c = tmpcp1+1;
					//find context ID
					tmpcp = strstr(c,"C=");

					if(tmpcp)
					{
						tmpcp1 = strcasestr(c,"{");
						strncpy(req->contextId,tmpcp+2,(strlen(tmpcp)-strlen(tmpcp1)-2));
						c = tmpcp1+1;

						//find Reply command ID
						tmpcp = strcasestr(c,"MF=");
						if(tmpcp)
						{
							tmpcp1 = strstr(c,"}");
							if(tmpcp1)
							{
								strncpy(req->notifyId,tmpcp+3,(strlen(tmpcp)-strlen(tmpcp1)-3));
								ast_verb(3,"Reply Modify receive %s \n",req->notifyId);
							}
							req->cmd = 	MEGACO_MODIFY;
							return;
						}
						//find Reply command ID
						tmpcp = strcasestr(c,"ER=");
						if(tmpcp)
						{
							tmpcp1 = strstr(c,"{");
							//strncpy(req->errorId,tmpcp+3,(strlen(tmpcp)-strlen(tmpcp1)-3));
							ast_verb(3,"Reply wirh Error ***************************  <%s> %d %d  \n",req->errorId,strlen(tmpcp),strlen(tmpcp1));
							req->cmd = 	MEGACO_ERROR;
							c = tmpcp1+1;
							//must chack latter for more detail such as command reply,......

							return;
						}

						tmpcp = strcasestr(c,"A=");
						if(tmpcp)
						{
							tmpcp1 = strcasestr(c,",A=");
							strncpy(req->notifyId,tmpcp+2,(strlen(tmpcp)-strlen(tmpcp1)-2));
							c = tmpcp1+1;
							tmpcp = strcasestr(c,"A=");
							if(tmpcp)
							{
								tmpcp1 = strcasestr(c,"{M{O");

								if(!tmpcp1)
									tmpcp1 = strcasestr(c,"{M{st=1{L");

								if(!tmpcp1)
								   tmpcp1 = strcasestr(c,"{M{L");

								if(tmpcp1)
								{
									strncpy(req->ephermalId,tmpcp+2,(strlen(tmpcp)-strlen(tmpcp1)-2));
								}
								else
								{
									ast_verb(3,"**hhh****** Add reply Error parse %s  tmpcp1:%s \n",c,tmpcp1);
									return;
								}

							}
							c = tmpcp1+1;

							//initialize to rtp l param
							c= strcasestr(c,"L");
							//ast_verb(3,"\nLLLLLLLLLLL %s %d \n",c,strlen(c));
							tmpcp = strcasestr(c,"L{");
							//ast_verb(3,"??????? %s %d \n",tmpcp,strlen(tmpcp));
							if(tmpcp)
							{
								tmpcp1 = strstr(c,"}");
								//ast_verb(3,"???????:::: %s %d \n",tmpcp1,strlen(tmpcp1));
								strncpy(req->rtpLparam,tmpcp+2,(strlen(tmpcp)-strlen(tmpcp1)-2));
							}

							ast_verb(3,"Add <%s>:Ephermal:<%s>\n",req->notifyId,req->ephermalId);
							/* Now we process any mime content */
							f = 0;
							req->line[f] = req->rtpLparam;
							//ast_verb(3,"------ parse up SDP line param -------\n<%s>\n",req->line[f]);
							for (; *c; c++) {
									if (*c == '\n') {
										/* We've got a new line */
										*c = 0;
										//ast_verb(3, "Line: %s (%d)\n", req->line[f], (int) strlen(req->line[f]));
										if (f >= MGCP_MAX_LINES - 1) {
											ast_log(LOG_WARNING, "Too many SDP lines...\n");
										} else {
											f++;
										}
										req->line[f] = c + 1;
									} else if (*c == '\r') {
										/* Ignore and eliminate \r's */
										*c = 0;
									}
								}
								/* Check for last line */
								if (!ast_strlen_zero(req->line[f])) {
									f++;
								}
								req->lines = f;

								/*if(req->lines==6)
								{
									req->lines =5;
									req->line[5]='\0';
								}*/




							req->cmd = 	MEGACO_ADD;
							//c = tmpcp1+1;

							return;
						}
						
						tmpcp = strcasestr(c,"s=");
						if(tmpcp)
						{
							ast_verb(3, "------------------Subtract Command\n");
							req->cmd =MEGACO_SUBTRACT;
							return;
						}
						tmpcp = strcasestr(c,"av=");
						if(tmpcp)
						{
							tmpcp1 = strstr(c,"}");
							if(tmpcp1)
							{
								strncpy(req->notifyId,tmpcp+3,(strlen(tmpcp)-strlen(tmpcp1)-3));
								ast_verb(3,"Reply Audit receive %s \n",req->notifyId);
							}
							req->cmd =MEGACO_AUDIT;
							ast_verb(3, "-----------------------------Audit Reply\n");
							return;
						}
					}



				}
				else
				{
					//unhandled megaco message
					req->transactionFlag = 2;
					ast_log(LOG_WARNING, "megaco command Errror %s \n", c);
					ast_verb(3, "megaco command Errror %s \n", c);
				}

			}

		break;
	}		

}

static int process_sdp(struct megaco_subchannel *sub, struct megaco_request *req)
{
	char *m;
	char *c;
	char *a;
	char host[258];
	int len = 0;
	int portno;
	struct ast_format_cap *peercap;
	int peerNonCodecCapability;
	struct sockaddr_in sin;
	struct ast_sockaddr sin_tmp;
	char *codecs;
	struct ast_hostent ahp; struct hostent *hp;
	int codec, codec_count=0;
	int iterator;
	struct megaco_users *p = sub->parent;
	char tmp1[256], tmp2[256], tmp3[256];


	/* Get codec and RTP info from SDP */
	m = get_sdp(req, "m");
	c = get_sdp(req, "c");
	if (ast_strlen_zero(m) || ast_strlen_zero(c)) {
		ast_log(LOG_WARNING, "Insufficient information for SDP (m = '%s', c = '%s')\n", m, c);
		return -1;
	}
	if (sscanf(c, "IN IP4 %256s", host) != 1) {
		ast_log(LOG_WARNING, "Invalid host in c= line, '%s'\n", c);
		return -1;
	}
	/* XXX This could block for a long time, and block the main thread! XXX */
	hp = ast_gethostbyname(host, &ahp);
	if (!hp) {
		ast_log(LOG_WARNING, "Unable to lookup host in c= line, '%s'\n", c);
		return -1;
	}
	if (sscanf(m, "audio %30d RTP/AVP %n", &portno, &len) != 1 || !len) {
		ast_log(LOG_WARNING, "Malformed media stream descriptor: %s\n", m);
		return -1;
	}

	sin.sin_family = AF_INET;
	memcpy(&sin.sin_addr, hp->h_addr, sizeof(sin.sin_addr));
	sin.sin_port = htons(portno);
	ast_sockaddr_from_sin(&sin_tmp, &sin);

	ast_rtp_instance_set_remote_address(sub->rtp, &sin_tmp);
	ast_verb(3, "Peer RTP is at port %s:%d\n", ast_inet_ntoa(sin.sin_addr), ntohs(sin.sin_port));

	/* Scan through the RTP payload types specified in a "m=" line: */
	ast_rtp_codecs_payloads_clear(ast_rtp_instance_get_codecs(sub->rtp), sub->rtp);
	codecs = ast_strdupa(m + len);
	while (!ast_strlen_zero(codecs)) {
		if (sscanf(codecs, "%30d%n", &codec, &len) != 1) {
			if (codec_count) {
				break;
			}
			ast_log(LOG_WARNING, "Error in codec string '%s' at '%s'\n", m, codecs);
			return -1;
		}
		ast_rtp_codecs_payloads_set_m_type(ast_rtp_instance_get_codecs(sub->rtp), sub->rtp, codec);
		codec_count++;
		codecs += len;
	}

	/* Next, scan through each "a=rtpmap:" line, noting each */
	/* specified RTP payload type (with corresponding MIME subtype): */
	sdpLineNum_iterator_init(&iterator);
	while ((a = get_sdp_iterate(&iterator, req, "a"))[0] != '\0') {
		char* mimeSubtype = ast_strdupa(a); /* ensures we have enough space */
		if (sscanf(a, "rtpmap: %30u %127[^/]/", &codec, mimeSubtype) != 2)
			continue;
		/* Note: should really look at the 'freq' and '#chans' params too */
		ast_rtp_codecs_payloads_set_rtpmap_type(ast_rtp_instance_get_codecs(sub->rtp), sub->rtp, codec, "audio", mimeSubtype, 0);
	}

	/* Now gather all of the codecs that were asked for: */
	if (!(peercap = ast_format_cap_alloc_nolock())) {
		return -1;
	}
	ast_rtp_codecs_payload_formats(ast_rtp_instance_get_codecs(sub->rtp), peercap, &peerNonCodecCapability);
	ast_format_cap_joint_copy(global_capability, peercap, p->cap);
	ast_debug(1, "Capabilities: us - %s, them - %s, combined - %s\n",
		ast_getformatname_multiple(tmp1, sizeof(tmp1), global_capability),
		ast_getformatname_multiple(tmp2, sizeof(tmp2), peercap),
		ast_getformatname_multiple(tmp3, sizeof(tmp3), p->cap));
	peercap = ast_format_cap_destroy(peercap);

	ast_verb(3, "Non-codec capabilities: us - %d, them - %d, combined - %d\n",
		nonCodecCapability, peerNonCodecCapability, p->nonCodecCapability);
	if (ast_format_cap_is_empty(p->cap)) {
		ast_log(LOG_WARNING, "No compatible codecs!\n");
		return -1;
	}

	return 0;
}
static int add_header_i(struct megaco_request *req, const char *var, unsigned int value)
{

	if (req->len >= sizeof(req->data) - 4) {
		ast_log(LOG_WARNING, "Out of space, can't add anymore\n");
		return -1;
	}
	if (req->lines) {
		ast_log(LOG_WARNING, "Can't add more headers when lines have been added\n");
		return -1;
	}
	req->header[req->headers] = req->data + req->len;
	snprintf(req->header[req->headers], sizeof(req->data) - req->len, "%s%d{", var, value);
	req->len += strlen(req->header[req->headers]);
	if (req->headers < MGCP_MAX_HEADERS) {
		req->headers++;
	} else {
		ast_log(LOG_WARNING, "Out of header space\n");
		return -1;
	}
	return 0;
}
static int add_header_n1(struct megaco_request *req, const char *var, const char *value)
{

	if (req->len >= sizeof(req->data) - 4) {
		ast_log(LOG_WARNING, "Out of space, can't add anymore\n");
		return -1;
	}
	if (req->lines) {
		ast_log(LOG_WARNING, "Can't add more headers when lines have been added\n");
		return -1;
	}
	req->header[req->headers] = req->data + req->len;
	snprintf(req->header[req->headers], sizeof(req->data) - req->len, "%s%s", var, value);
	req->len += strlen(req->header[req->headers]);
	if (req->headers < MGCP_MAX_HEADERS) {
		req->headers++;
	} else {
		ast_log(LOG_WARNING, "Out of header space\n");
		return -1;
	}
	return 0;
}

static int add_header(struct megaco_request *req, const char *var, const char *value)
{

	if (req->len >= sizeof(req->data) - 4) {
		ast_log(LOG_WARNING, "Out of space, can't add anymore\n");
		return -1;
	}
	if (req->lines) {
		ast_log(LOG_WARNING, "Can't add more headers when lines have been added\n");
		return -1;
	}
	req->header[req->headers] = req->data + req->len;
	snprintf(req->header[req->headers], sizeof(req->data) - req->len, "%s%s{", var, value);
	req->len += strlen(req->header[req->headers]);
	if (req->headers < MGCP_MAX_HEADERS) {
		req->headers++;
	} else {
		ast_log(LOG_WARNING, "Out of header space\n");
		return -1;
	}
	return 0;
}

static int add_line(struct megaco_request *req, char *line)
{
    //ast_verb(3,"--add_line :%d  > %s ",req->lines,line);

	if (req->len >= sizeof(req->data) - 4) {
			ast_log(LOG_WARNING, "Out of space, can't add anymore\n");
			return -1;
		}
		if (!req->lines) {
			/* Add extra empty return */
			ast_copy_string(req->data + req->len, "\r\n", sizeof(req->data) - req->len);
			req->len += strlen(req->data + req->len);
		}
		req->line[req->lines] = req->data + req->len;
		snprintf(req->line[req->lines], sizeof(req->data) - req->len, "%s", line);
		req->len += strlen(req->line[req->lines]);
		if (req->lines < MGCP_MAX_LINES) {
			req->lines++;
		} else {
			ast_log(LOG_WARNING, "Out of line space\n");
			return -1;
		}
		//ast_verb(3,"---add_line : %d > %s ",req->lines,req->line[req->lines-1]);
		return 0;
}

static int init_resp(struct megaco_request *req, char *resp, struct megaco_request *orig, char *resprest)
{

	/* Initialize a response */
		if (req->headers || req->len) {
			ast_log(LOG_WARNING, "Request already initialized?!?\n");
			return -1;
		}
		req->header[req->headers] = req->data + req->len;
		snprintf(req->header[req->headers], sizeof(req->data) - req->len, "%s %s %s\r\n", resp, orig->identifier, resprest);
		req->len += strlen(req->header[req->headers]);
		if (req->headers < MGCP_MAX_HEADERS) {
			req->headers++;
		} else {
			ast_log(LOG_WARNING, "Out of header space\n");
		}
		return 0;
}

static int init_req(struct megaco_users *p, struct megaco_request *req, char *verb)
{
	/* Initialize a response */
		if (req->headers || req->len) {
			ast_log(LOG_WARNING, "Request already initialized?!?\n");
			return -1;
		}
		req->header[req->headers] = req->data + req->len;
		/* check if we need brackets around the gw name */
		if (p->parent->isnamedottedip) {
			snprintf(req->header[req->headers], sizeof(req->data) - req->len, "%s %u %s@[%s] MGCP 1.0%s\r\n", verb, oseq, p->name, p->parent->name, p->ncs ? " NCS 1.0" : "");
		} else {
	+		snprintf(req->header[req->headers], sizeof(req->data) - req->len, "%s %u %s@%s MGCP 1.0%s\r\n", verb, oseq, p->name, p->parent->name, p->ncs ? " NCS 1.0" : "");
		}
		req->len += strlen(req->header[req->headers]);
		if (req->headers < MGCP_MAX_HEADERS) {
			req->headers++;
		} else {
			ast_log(LOG_WARNING, "Out of header space\n");
		}
		return 0;
}


static int respprep(struct megaco_request *resp, struct megaco_users *p, char *msg, struct megaco_request *req, char *msgrest)
{
	memset(resp, 0, sizeof(*resp));
	init_resp(resp, msg, req, msgrest);
	return 0;
}

static int reqprep(struct megaco_request *req, struct megaco_users *p, char *verb)
{
	unsigned int oseq;
		memset(req, 0, sizeof(struct megaco_request));
		ast_mutex_lock(&oseq_lock);
		oseq_global++;
		if (oseq_global > 999999999) {
			oseq_global = 1;
		}
		oseq = oseq_global;
		ast_mutex_unlock(&oseq_lock);
		init_req(p, req, verb);//   , oseq);
		return oseq;
}

static int transmit_response(struct megaco_subchannel *sub, char *msg, struct megaco_request *req, char *msgrest)
{
	struct megaco_request resp;
	struct megaco_users *p = sub->parent;
	struct megaco_response *mgr;



	return 0;
}


static int transmit_modify_with_sdp(struct megaco_subchannel *sub, struct ast_rtp_instance *rtp, const struct ast_format_cap *codecs)
{
	struct megaco_request resp;
	char local[256];
	char tmp[80];
	struct megaco_users *p = sub->parent;
	struct ast_format tmpfmt;
	struct ast_sockaddr sub_tmpdest_tmp;


	return 0;
}


static int transmit_connect(struct megaco_subchannel *sub)
{
	struct megaco_request resp;
	char local[256];
	char tmp[80];
	struct ast_format tmpfmt;
	struct megaco_users *p = sub->parent;
	ast_verb(3,"-------------------transmit_connect\n");

	return 0;
}

static int transmit_notify_request(struct megaco_subchannel *sub, char *tone)
{
	struct megaco_request resp;
	struct megaco_users *p = sub->parent;


	return 0;
}
//
//static int transmit_serviceChangeToMg(struct megaco_request *req,int kflag)
//{
//	struct megaco_request resp;
//	int len  = len = sizeof(req->sin);
//	int res;
//	memset(&resp, 0, sizeof(resp));
//
//
//	char v[256];
//	char *h;
//	int i=0;
//	snprintf(v, sizeof(v),"[%s]:2944 ",  megacomg->addr.sin_addr.s_addr ? ast_inet_ntoa(megacomg->addr.sin_addr) : ast_inet_ntoa(megacomg->defaddr.sin_addr));
//
//	add_header_n1(&resp, "!/1 ", v);
//	add_header_i(&resp, "T=", megaco_req_id++);
//	add_header(&resp, "C=", req->contextId);
//	add_header_n1(&resp, "SC=", "A103");//req->servicechangeId);
//	add_header_n1(&resp, "{SV{MT=RS,RE=900}","}");
//
//	add_header_n1(&resp, "}", "}");
//
//	ast_verb(3," transmit will be ready resp.data:\n%s \n",resp.data);
//
//	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&req->sin), len);
//	ast_verb(3,"transmit done :%d\n",res);
//
//	return 0;
//}


static int transmit_serviceChangeReply(struct megaco_request *req,int kflag,struct megaco_subchannel *sub )
{
	struct megaco_request resp;
	int res;
	memset(&resp, 0, sizeof(resp));

	int len = sizeof(req->sin);
    struct megaco_mg *mg = sub->parent->parent;

	char v[256];
	char *h;
	int i=0;
	snprintf(v, sizeof(v),"[%s]:2944 ",ast_inet_ntoa(bindaddr.sin_addr));//  megacomg->addr.sin_addr.s_addr ? ast_inet_ntoa(megacomg->addr.sin_addr) : ast_inet_ntoa(megacomg->defaddr.sin_addr));

	add_header_n1(&resp, "!/1 ", v);
	add_header(&resp, "P=", req->transactionIDtext);
	add_header(&resp, "C=", req->contextId);
	add_header_n1(&resp, "SC=", req->servicechangeId);
//	add_header_n1(&resp, "{SV{V=1}", "}");  //chanage for huawei mazandaran  megacomg-> >mg_version
	
	//Add mg->version in reply 
	add_header_n1(&resp, "{SV{V=", megacomg->mg_version);
	add_header_n1(&resp, "}", "}");  

/*
	if(kflag)
	{
		add_header_n1(&resp, "{SV{MT=RS,RE=900}}}", "}");
		add_header_n1(&resp, "\nK{", req->kvalueId);
		add_header_n1(&resp, "", "}");
	}
	else*/

	add_header_n1(&resp, "}", "}");
	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&req->sin), len);
	if (mgcpdebug)
			ast_verb(3,"<res:%d ,V=%s> Service change Reply will be: %s \n",res,megacomg->mg_version,resp.data);

	return 0;
}

static int transmit_ResponseAck(struct megaco_request *req)
{
	struct megaco_request resp;
	int len  = len = sizeof(req->sin);
	int res;
	memset(&resp, 0, sizeof(resp));


	char v[256];
	char *h;
	int i=0;
	snprintf(v, sizeof(v),"[%s]:2944 ",ast_inet_ntoa(bindaddr.sin_addr));
	add_header_n1(&resp, "!/1 ", v);
	add_header_n1(&resp, "K{", req->replyId);
	add_header_n1(&resp, "", "}");

	if (mgcpdebug)
		ast_verb(3," ResponseAck will be: %s \n",resp.data);
	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&req->sin), len);
	//ast_verb(3,"transmit done :%d\n",res);

	return 0;


}
static int transmit_notify_resp(struct megaco_request *req,struct megaco_subchannel *sub)
{
	struct megaco_request resp;
	int len  = len = sizeof(req->sin);
	int res;
	memset(&resp, 0, sizeof(resp));
	struct megaco_mg *mg = sub->parent->parent;

	char v[256];
	char *h;
	int i=0;
	snprintf(v, sizeof(v),"[%s]:2944 ",mg->domain);//  megacomg->addr.sin_addr.s_addr ? ast_inet_ntoa(megacomg->addr.sin_addr) : ast_inet_ntoa(megacomg->defaddr.sin_addr));

	add_header_n1(&resp, "!/1 ", v);
	add_header(&resp, "P=", req->transactionIDtext);
	add_header(&resp, "C=", req->contextId);
	add_header_n1(&resp, "N=", req->notifyId);
	//add_header_n1(&resp, "SV{MT=RS,V=2}", "}}}");
	add_header_n1(&resp, "}", "}");

	if (mgcpdebug)
		ast_verb(3," Notify Reaponse will be: %s \n",resp.data);
	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&req->sin), len);
	//ast_verb(3,"transmit done :%d\n",res);

	return 0;



}
static int  transmit_AddChooseOutgoing(struct megaco_request *req,char *destId,struct megaco_subchannel *sub)
{
	struct megaco_request resp;
	int len  = len = sizeof(req->sin);
	int res;
	memset(&resp, 0, sizeof(resp));

    struct megaco_mg *mg = sub->parent->parent;
	char v[256];
	char *h;
	int i=0;
	snprintf(v, sizeof(v),"[%s]:2944 ",mg->domain);//  megacomg->addr.sin_addr.s_addr ? ast_inet_ntoa(megacomg->addr.sin_addr) : ast_inet_ntoa(megacomg->defaddr.sin_addr));

	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);//req->transactionIDtext);

	add_header(&resp, "C=","$");// req->contextId);
	add_header_n1(&resp, "A=", req->notifyId);
	add_header_n1(&resp, "{M{O{MO=SR}}", "}");
	add_header_n1(&resp, ",A=", destId);
	add_header_n1(&resp, "{M{O{MO=SR}}", "}");


	add_header_n1(&resp, "}", "}");

	if (mgcpdebug)
		ast_verb(3,"Add Choosing Outgoing will be ready:  %s \n",resp.data);
	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&req->sin), len);


	return 0;

}

static int  transmit_AddSipChooseOutgoing(struct megaco_request *req,char *destId,struct megaco_subchannel *sub)
{
	//under check????????????????OKKKKKKKKKKKKKK
	struct megaco_request resp;

	int res;
	memset(&resp, 0, sizeof(resp));
    struct megaco_mg *mg = sub->parent->parent;
    int  len = sizeof(mg->addr);
	char v[256];
	char *h;
	int i=0;
	snprintf(v, sizeof(v),"[%s]:2944 ",mg->domain);

	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);

	add_header(&resp, "C=","$");
	add_header_n1(&resp, "A=", destId);
	add_header_n1(&resp, "{M{O{MO=SR,RV=OFF,RG=OFF}},E=2222{al/*},SG{}", "},");
	add_header_n1(&resp, "A=","$");
	add_header_n1(&resp, "{M{O{MO=IN,RV=OFF,RG=OFF,nt/jit=40},L{v=0\r\nc=IN IP4 $\r\nm=audio $ RTP/AVP 8 18\r\na=ptime:20\r\n\n}}","}");
	add_header_n1(&resp, "}", "}");

	if (mgcpdebug)
		ast_verb(3," AddSipChooseOutgoing will be:%s \n",resp.data);
	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&mg->addr), len);
	//ast_verb(3,"transmit done :%d\n",res);

	return 0;

}


static int transmit_connectAB(struct megaco_request *req,char *AnotifyId,char *AcontextId,char *BnotifyId,char *BcontextId)
{

	struct megaco_request resp;
	int len  = len = sizeof(req->sin);
	int res;
	memset(&resp, 0, sizeof(resp));

		//struct megaco_users *p = sub->parent;
	char v[256];
	char *h;
	int i=0;
	snprintf(v, sizeof(v),"[%s]:2944 ",  megacomg->addr.sin_addr.s_addr ? ast_inet_ntoa(megacomg->addr.sin_addr) : ast_inet_ntoa(megacomg->defaddr.sin_addr));

	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);//req->transactionIDtext);
	add_header(&resp, "C=", BcontextId);
	add_header_n1(&resp, "A=",AnotifyId);
	add_header_n1(&resp, "}", "}");

	if (mgcpdebug)
		ast_verb(3,"transmit_connectAB <%s>:<%s> <****> <%s>:<%s> \nresp.data:\n%s \n",AnotifyId,AcontextId,BnotifyId,BcontextId,resp.data);

	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&req->sin), len);
	return 0;
}

static int transmit_InitailAllTermination(struct megaco_request *req,struct sockaddr_in *sin)
{

	struct megaco_users *p = NULL;
	struct megaco_subchannel *sub = NULL;
	struct megaco_mg *g;
	char tmp[256] = "";
	char *at = NULL, *c;
	int found = 0;

	char destIp[128];

	snprintf(destIp,sizeof(destIp),"%s",ast_inet_ntoa(sin->sin_addr));


	for (g = megacomg ;g;g = g->next){
		for (p = g->endpoints; p; p = p->next) {
			if((!strcmp(destIp,ast_inet_ntoa( p->parent->addr.sin_addr))))
			{
				ast_verb(3,"--OK ----------find %s at %s in %s :%s <%s>\n",p->name,g->domain,g->name,ast_inet_ntoa(g->addr.sin_addr),ast_inet_ntoa(sin->sin_addr));
				transmit_ModifyAll("-",p->name,&req->sin);
				p->callstate = MG_AWAIT_INIT_OK_ST;
			}

		}
	}



}

static int transmit_ModifyAll(char *contextId,char *notifyId,struct sockaddr_in *sin)
{
	    struct megaco_request resp;
		int res;
		int len;
		memset(&resp, 0, sizeof(resp));
		len=sizeof(struct sockaddr_in);
		char v[256];
		char *h;
		int i=0;
		snprintf(v, sizeof(v),"[%s]:2944 ",ast_inet_ntoa(bindaddr.sin_addr));

		add_header_n1(&resp, "!/1 ", v);
	    add_header_i(&resp, "T=", megaco_req_id++);
		add_header(&resp, "C=", contextId);
		//add_header_n1(&resp, "MF=", "*{E=524290139{al/*},SG{}}");
		add_header_n1(&resp, "MF=",notifyId);
		add_header_n1(&resp, "{E=2222{al/*},SG{}", "}");


		add_header_n1(&resp, "}", "}");
		res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (sin), len);

		if (mgcpdebug)
				ast_verb(3,"<res: %d> Modify will be: %s (al/*)  \n",res,resp.data);
		return 0;
}


static int transmit_ModifyOneSubChannel(char *contextId,char *name, struct megaco_subchannel *sub)
{
	struct megaco_request resp;
	int res;
	memset(&resp, 0, sizeof(resp));

	struct megaco_mg *mg = sub->parent->parent;
	int len  = sizeof(mg->addr);

	char v[256];
	char ldmap[256];
	char *h;
	int i=0;

	snprintf(v, sizeof(v),"[%s]:2944 ", mg->domain);// mg->addr.sin_addr.s_addr ? ast_inet_ntoa(mg->addr.sin_addr) : ast_inet_ntoa(mg->defaddr.sin_addr));
	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);
	add_header(&resp, "C=", contextId);
	//add_header_n1(&resp, "MF=", "*{E=524290139{al/*},SG{}}");
	add_header_n1(&resp, "MF=",name);
	add_header_n1(&resp, "{E=2223{al/*},SG{}", "}");


	add_header_n1(&resp, "}", "}");
    res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&mg->addr), len);

	if (mgcpdebug)
				ast_verb(3,"<res: %d> Modify will be: %s (al/*)  \n",res,resp.data);
	return 0;

}
static int publish_expire(const void *data)
{
	struct megaco_subchannel *sub = (struct megaco_subchannel *) data;

	ast_verb(3,"test static int publish_expire :%d for :%s  @%s  Wait:%d \n",sub->sch_id,sub->parent->name,sub->parent->parent->name,sub->AuditRetansCount);

	if(sub->AuditRetansCount<10)
    {
            transmit_AuditRoot(sub);
            sub->AuditRetansCount++;
    }
    else
    {
        ast_verb(3,"MG : %s@%s  Wait:%d \n",sub->parent->name,sub->parent->parent->name,sub->AuditRetansCount);
    	sub->AuditRetansCount=0;
        sub->parent->callstate = MG_BROKEN_ST;
        return 0 ;
    }

	return sub->sch_id;
}

static int transmit_MgAuditRoot(struct megaco_subchannel *sub)
{
	struct megaco_request resp;
	int res;
	memset(&resp, 0, sizeof(resp));

	struct megaco_mg *mg = sub->parent->parent;
	int len  = sizeof(mg->addr);

	char v[256];
	char ldmap[256];
	char *h;
	int i=0;

	snprintf(v, sizeof(v),"[%s]:2944 ", mg->domain);// mg->addr.sin_addr.s_addr ? ast_inet_ntoa(mg->addr.sin_addr) : ast_inet_ntoa(mg->defaddr.sin_addr));

	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);
	add_header(&resp, "C=", "-");
	add_header_n1(&resp, "AV=","ROOT{AT{}}");


	add_header_n1(&resp, "}", "}");

	if (mgcpdebug)
		ast_verb(3," MgCheckAlliveMGC will be: %s \n",resp.data);

	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&mg->addr), len);



    //MG Add for
	//megaco_postrequest(sub->parent,sub, resp.data,resp.len, 0);

     sub->sch_id = ast_sched_add(sched, MEGACO_AUDIT_RETRANS, publish_expire, sub);
    //   ast_verb(3,"**We are heare..............mm.................................>>%d\n",sub->sch_id);


	return 0;

}
static int transmit_AuditRoot(struct megaco_subchannel *sub)
{
    struct megaco_request resp;
    int res;
    memset(&resp, 0, sizeof(resp));

    struct megaco_mg *mg = sub->parent->parent;
    int len  = sizeof(mg->addr);

    char v[256];
    char ldmap[256];
    char *h;
    int i=0;

    snprintf(v, sizeof(v),"[%s]:2944 ", mg->domain);// mg->addr.sin_addr.s_addr ? ast_inet_ntoa(mg->addr.sin_addr) : ast_inet_ntoa(mg->defaddr.sin_addr));

    add_header_n1(&resp, "!/1 ", v);
    add_header_i(&resp, "T=", megaco_req_id++);
    add_header(&resp, "C=", "-");
    add_header_n1(&resp, "AV=","ROOT{AT{}}");


    add_header_n1(&resp, "}", "}");

    if (mgcpdebug)
            ast_verb(3," MgCheckAlliveMGC will be: %s \n",resp.data);

    res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&mg->addr), len);


    return 0;


}
static int transmit_ModifyPalyCrbt(struct megaco_request *req,char *contextId,char *notifyId,struct megaco_subchannel *sub,struct megaco_subchannel *b_sub)
{
	struct megaco_request resp;
	int len  = 0;
	int res;
	memset(&resp, 0, sizeof(resp));
    struct megaco_mg *mg = sub->parent->parent;

    len = sizeof(mg->addr);
	char v[256],rtp[128];
	char *h;
	int i=0;
	snprintf(v, sizeof(v),"[%s]:2944 ", mg->domain);// megacomg->addr.sin_addr.s_addr ? ast_inet_ntoa(megacomg->addr.sin_addr) : ast_inet_ntoa(megacomg->defaddr.sin_addr));

	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);//req->transactionIDtext);
	add_header(&resp, "C=", contextId);


	add_header(&resp, "MF=",sub->parent->ephermalId);

	add_header_n1(&resp,"M{O{MO=SR}","");
	//,L{v=0\r\nc=IN IP4 -\r\nm=audio - RTP/AVP 8 18\r\na=ptime:20 \r\n\n}
	snprintf(rtp,sizeof(rtp),"v=0\r\nc=IN IP4 %s \r\nm=audio %d RTP/AVP 8 18\r\n\n",ast_inet_ntoa(bindaddr.sin_addr),sub->moh_port);
	add_header_n1(&resp,",R{",rtp);

	//add_header_n1(&resp,",R{","v=0\r\nc=IN IP4 192.168.2.58 \r\nm=audio 9080 RTP/AVP 8 \r\n\n");//b_sub->parent->rtpLparam);
	add_header_n1(&resp,"}}","}");

	add_header_n1(&resp, "}", "}");

	if (mgcpdebug)
		ast_verb(3,"transmit_ModifyPalyCrbt <%s>:<%s>  %s \n",notifyId,contextId,resp.data);
	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&mg->addr), len);

	return 0;


}

static int transmit_ModifyTdmNoSignalWithSDP_1(struct megaco_request *req,char *contextId,char *notifyId,struct megaco_subchannel *sub,struct megaco_subchannel *b_sub)
{
	struct megaco_request resp;
	int len  = 0;
	int res;
	memset(&resp, 0, sizeof(resp));
    struct megaco_mg *mg = sub->parent->parent;

    len = sizeof(mg->addr);
	char v[256],rtp[128];
	char *h;
	int i=0;
	snprintf(v, sizeof(v),"[%s]:2944 ", mg->domain);// megacomg->addr.sin_addr.s_addr ? ast_inet_ntoa(megacomg->addr.sin_addr) : ast_inet_ntoa(megacomg->defaddr.sin_addr));

	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);//req->transactionIDtext);
	add_header(&resp, "C=", contextId);
	add_header(&resp, "MF=",notifyId);
	add_header_n1(&resp,"M{O{MO=SR,RV=OFF,RG=OFF,tdmc/ec=ON","}},");
	add_header(&resp, "E=", "2223");
	add_header_n1(&resp, "al/*},SG{}", "}");

	add_header(&resp, ",MF=",sub->parent->ephermalId);
	//add_header_n1(&resp,"M{O{MO=SR,RV=OFF,RG=OFF},L{v=0\r\nc=IN IP4 -\r\nm=audio - RTP/AVP 8 \r\n\n}","}}");
	add_header_n1(&resp,"M{O{MO=SR,RV=OFF,RG=OFF}","");
	//,L{v=0\r\nc=IN IP4 -\r\nm=audio - RTP/AVP 8 18\r\na=ptime:20 \r\n\n}
	snprintf(rtp,sizeof(rtp),"v=0\r\nc=IN IP4 %s \r\nm=audio %d RTP/AVP 8 18\r\n\n",ast_inet_ntoa(sub->rtp_remote_sin.sin_addr), ntohs(sub->rtp_remote_sin.sin_port));
	add_header_n1(&resp,",R{",rtp);

	//add_header_n1(&resp,",R{","v=0\r\nc=IN IP4 192.168.2.58 \r\nm=audio 9080 RTP/AVP 8 \r\n\n");//b_sub->parent->rtpLparam);
	add_header_n1(&resp,"}}","}");




	add_header_n1(&resp, "}", "}");

	if (mgcpdebug)
		ast_verb(3,"ModifyTdmNoSignal_1 <%s>:<%s>  %s \n",notifyId,contextId,resp.data);
	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&mg->addr), len);

	return 0;



}
static int transmit_ModifyTdmNoSignalWithSDP_2(struct megaco_request *req,char *contextId,char *notifyId,struct megaco_subchannel *sub,struct megaco_subchannel *b_sub)
{
	//receive only on SDP
	struct megaco_request resp;
	int len  = 0;
	int res;
	memset(&resp, 0, sizeof(resp));
    struct megaco_mg *mg = sub->parent->parent;

    len = sizeof(mg->addr);
	char v[256],rtp[128];
	char *h;
	int i=0;
	snprintf(v, sizeof(v),"[%s]:2944 ", mg->domain);// megacomg->addr.sin_addr.s_addr ? ast_inet_ntoa(megacomg->addr.sin_addr) : ast_inet_ntoa(megacomg->defaddr.sin_addr));

	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);//req->transactionIDtext);
	add_header(&resp, "C=", contextId);
	add_header(&resp, "MF=",notifyId);
	add_header_n1(&resp,"M{O{MO=RC,RV=OFF,RG=OFF,tdmc/ec=ON","}},");
	add_header(&resp, "E=", "2223");
	add_header_n1(&resp, "al/*},SG{}", "}");

	add_header(&resp, ",MF=",sub->parent->ephermalId);
	//add_header_n1(&resp,"M{O{MO=SR,RV=OFF,RG=OFF},L{v=0\r\nc=IN IP4 -\r\nm=audio - RTP/AVP 8 \r\n\n}","}}");
	add_header_n1(&resp,"M{O{MO=RC,RV=OFF,RG=OFF}","");
	//,L{v=0\r\nc=IN IP4 -\r\nm=audio - RTP/AVP 8 18\r\na=ptime:20 \r\n\n}
	snprintf(rtp,sizeof(rtp),"v=0\r\nc=IN IP4 %s \r\nm=audio %d RTP/AVP 8 18\r\n\n",ast_inet_ntoa(sub->rtp_remote_sin.sin_addr), ntohs(sub->rtp_remote_sin.sin_port));
	add_header_n1(&resp,",R{",rtp);

	//add_header_n1(&resp,",R{","v=0\r\nc=IN IP4 192.168.2.58 \r\nm=audio 9080 RTP/AVP 8 \r\n\n");//b_sub->parent->rtpLparam);
	add_header_n1(&resp,"}}","}");




	add_header_n1(&resp, "}", "}");

	if (mgcpdebug)
		ast_verb(3,"ModifyTdmNoSignal_2 <%s>:<%s>  %s \n",notifyId,contextId,resp.data);
	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&mg->addr), len);

	return 0;



}
static int transmit_ModifyTdmNoSignalWithSDP(struct megaco_request *req,char *contextId,char *notifyId,struct megaco_subchannel *sub,struct megaco_subchannel *b_sub)
{
	struct megaco_request resp;
	int len  = 0;
	int res;
	memset(&resp, 0, sizeof(resp));
    struct megaco_mg *mg = sub->parent->parent;

    len = sizeof(mg->addr);
	char v[256],rtp[128];
	char *h;
	int i=0;
	snprintf(v, sizeof(v),"[%s]:2944 ", mg->domain);// megacomg->addr.sin_addr.s_addr ? ast_inet_ntoa(megacomg->addr.sin_addr) : ast_inet_ntoa(megacomg->defaddr.sin_addr));

	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);//req->transactionIDtext);
	add_header(&resp, "C=", contextId);
	add_header(&resp, "MF=",notifyId);
	add_header_n1(&resp,"M{O{MO=SR,RV=OFF,RG=OFF,tdmc/ec=ON","}},");
	add_header(&resp, "E=", "2223");
	add_header_n1(&resp, "al/*},SG{}", "}");

	add_header(&resp, ",MF=",sub->parent->ephermalId);
	//add_header_n1(&resp,"M{O{MO=SR,RV=OFF,RG=OFF},L{v=0\r\nc=IN IP4 -\r\nm=audio - RTP/AVP 8 \r\n\n}","}}");
	add_header_n1(&resp,"M{O{MO=SR,RV=OFF,RG=OFF}","");
	add_header_n1(&resp,",R{",b_sub->parent->rtpLparam);
	add_header_n1(&resp,"}}","}");

	add_header_n1(&resp, "}", "}");

	if (mgcpdebug)
		ast_verb(3,"ModifyTdmNoSignal_1 <%s>:<%s>  %s \n",notifyId,contextId,resp.data);
	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&mg->addr), len);

	return 0;



}

static int transmit_ModifyTdmNoSignal(struct megaco_request *req,char *contextId,char *notifyId,struct megaco_subchannel *sub)
{
	struct megaco_request resp;
	int len  = 0;
	int res;
	memset(&resp, 0, sizeof(resp));
    struct megaco_mg *mg = sub->parent->parent;

    len = sizeof(mg->addr);
	char v[256];
	char *h;
	int i=0;
	snprintf(v, sizeof(v),"[%s]:2944 ", mg->domain);// megacomg->addr.sin_addr.s_addr ? ast_inet_ntoa(megacomg->addr.sin_addr) : ast_inet_ntoa(megacomg->defaddr.sin_addr));

	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);//req->transactionIDtext);
	add_header(&resp, "C=", contextId);
	add_header(&resp, "MF=",notifyId);
	add_header(&resp, "E=", "2223");
	add_header_n1(&resp, "al/of,al/on,al/fl},SG{}", "}");

	add_header_n1(&resp, "}", "}");

	if (mgcpdebug)
		ast_verb(3,"ModifyTdmNoSignal <%s>:<%s>    %s \n",notifyId,contextId,resp.data);
	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&mg->addr), len);


	return 0;



}


//***********************************************************************************************
static int transmit_ModifyRingBackTone1(char *contextId,char *notifyId,struct megaco_subchannel *sub)
{
	struct megaco_request resp;

	int res;
	memset(&resp, 0, sizeof(resp));

	struct megaco_mg *mg = sub->parent->parent;
	int len  =  sizeof(mg->addr);

	char v[256];
	char *h;
	int i=0;
	snprintf(v, sizeof(v),"[%s]:2944 ",mg->domain);//  megacomg->addr.sin_addr.s_addr ? ast_inet_ntoa(megacomg->addr.sin_addr) : ast_inet_ntoa(megacomg->defaddr.sin_addr));

	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);//req->transactionIDtext);
	add_header(&resp, "C=", contextId);
	add_header(&resp, "MF=",notifyId);
	add_header_n1(&resp, "SG{cg/rt}", "}");
	add_header_n1(&resp, "}", "}");

	if (mgcpdebug)
		ast_verb(3,"ModifyRingBackTone1 will be:  %s \n",resp.data);
	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&mg->addr), len);

	return 0;

}

static int transmit_ModifyRingBackTone(struct megaco_request *req,struct megaco_subchannel *sub)
{
	struct megaco_request resp;
	int len  = sizeof(req->sin);
	int res;
	memset(&resp, 0, sizeof(resp));

    struct megaco_mg *mg = sub->parent->parent;
	char v[256];
	char *h;
	int i=0;
	snprintf(v, sizeof(v),"[%s]:2944 ", mg->domain);// megacomg->addr.sin_addr.s_addr ? ast_inet_ntoa(megacomg->addr.sin_addr) : ast_inet_ntoa(megacomg->defaddr.sin_addr));

	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);//req->transactionIDtext);

	add_header(&resp, "C=", req->contextId);
	add_header(&resp, "MF=", req->notifyId);
	add_header(&resp, "E=", "2223");
	add_header_n1(&resp, "al/*},SG{cg/rt}", "}");

	add_header_n1(&resp, "}", "}");

	if (mgcpdebug)
		ast_verb(3," ModifyRingBackTone will be: %s \n",resp.data);
	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&req->sin), len);


	return 0;



}

static int transmit_ModifyRing(struct megaco_request *req,struct megaco_subchannel *sub)
{
	//send ring to 	req->destId

	struct megaco_request resp;
	int len  = len = sizeof(req->sin);
	int res,cid_len;
	unsigned char cid_byte[32],sum,cid_checksum;

	memset(&resp, 0, sizeof(resp));

	struct megaco_mg *mg = sub->parent->parent;
	char v[256];

	char cid[256];
	int i=0;
	snprintf(v, sizeof(v),"[%s]:2944 ", mg->domain);// megacomg->addr.sin_addr.s_addr ? ast_inet_ntoa(megacomg->addr.sin_addr) : ast_inet_ntoa(megacomg->defaddr.sin_addr));

   /*cid format is  :type(04->sdmf) ,lenght, date,time,phonenumber (ascci format) ,checksum
                   The checksum value contains the twos complement of the modulo 256 sum of the other words in the data message (i.e., message type, message length, and data words). The receiving equipment
                   */
	sum =0 ;
    for(i=0;i<sub->cid_len;i++)
    {
	    ast_verb(3,"A[%d] : %x\n" , i, sub->cid_byte[i]);      
	}



    for(i=0;i<sub->cid_len;i++)
    {
    	sum +=	sub->cid_byte[i];
    }
    //Date  mounth  ,day
    sum +=	0x31;
	sum +=	0x31;
	sum +=	0x31;
	sum +=	0x37;	

    //Time  Hour,minute
    sum +=	0x31;
	sum +=	0x30;
	sum +=	0x32;
	sum +=	0x39;	
	
	sum +=	0x2B;
	
	cid_len  = i+8+1;  //8 becuaseof date-time 
	sum +=cid_len;

	sum +=0x04;  //message type

    cid_checksum = (~sum) +1   ;
    
	snprintf(cid,sizeof(cid),"%02x%02x%s%s%02x",4,cid_len,"31313137313032392B",sub->callid1,cid_checksum);


	//snprintf(cid,sizeof(cid),"%s%s31","041731303130313032392B",sub->callid1);
	
	
	ast_verb(3,"new  cid-->> CID send :%s len:%d  on  %s \n",cid,cid_len,sub->callid1);

//	ava_log("SIP|=|2|=|CID Megaco :%s len:%d  on  %s \n",cid,cid_len,sub->callid1);
	

	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);//req->transactionIDtext);
	add_header(&resp, "C=", req->contextId);
	add_header(&resp, "MF=", req->notifyId);//req->destId);
	add_header(&resp, "E=", "2222");
	add_header_n1(&resp, "al/of{strict=state},g/sc},SG{andisp/dwa{ddb=","");//
	add_header_n1(&resp,cid, ",pattern=1}}}");

			//,M{O{MO=SR} al/ri

	add_header_n1(&resp, "}", "}");

	if (mgcpdebug)
		ast_verb(3,"Modify Ring be: %s \n Call ID of<%s> IS:-%s-\n",resp.data,sub->parent->name,sub->callid1);
	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&req->sin), len);
	return 0;

}
//***********************************************************************************************
static int transmit_ModifyBusyTone(char *contextId,char *notifyId,struct megaco_subchannel *sub)
{
	struct megaco_request resp;

	int res;
	memset(&resp, 0, sizeof(resp));

	struct megaco_mg *mg = sub->parent->parent;
	int len  =  sizeof(mg->addr);

	char v[256];
	char *h;
	int i=0;
	snprintf(v, sizeof(v),"[%s]:2944 ",mg->domain);//  megacomg->addr.sin_addr.s_addr ? ast_inet_ntoa(megacomg->addr.sin_addr) : ast_inet_ntoa(megacomg->defaddr.sin_addr));

	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);//req->transactionIDtext);
	add_header(&resp, "C=", contextId);
	add_header(&resp, "MF=",notifyId);
	add_header_n1(&resp, "SG{cg/bt}", "}");
	add_header_n1(&resp, "}", "}");

	if (mgcpdebug)
		ast_verb(3,"Modify busy tone will be:  %s \n",resp.data);
	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&mg->addr), len);

	return 0;

}
//***********************************************************************************************
static int transmit_ModifyCallWaitingTone(char *contextId,char *notifyId,struct megaco_subchannel *sub)
{
	struct megaco_request resp;

	int res;
	memset(&resp, 0, sizeof(resp));

	struct megaco_mg *mg = sub->parent->parent;
	int len  =  sizeof(mg->addr);

	char v[256];
	char *h;
	int i=0;
	snprintf(v, sizeof(v),"[%s]:2944 ",mg->domain);//  megacomg->addr.sin_addr.s_addr ? ast_inet_ntoa(megacomg->addr.sin_addr) : ast_inet_ntoa(megacomg->defaddr.sin_addr));
	
	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);//req->transactionIDtext);
	add_header(&resp, "C=", contextId);
	add_header(&resp, "MF=",notifyId);
    add_header(&resp, "E=", "2222");
	add_header_n1(&resp, "al/fl, al/on},SG{cg/cw}", "}");
	add_header_n1(&resp, "}", "}");


	if (mgcpdebug)
		ast_verb(3,"Modify Call wating tone will be:  %s \n",resp.data);
	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&mg->addr), len);

	return 0;

}
//************************************************************************************************
static int transmit_ModifyPlayAnnouncment(struct megaco_request *req,struct megaco_subchannel *sub)
{
	struct megaco_request resp;
	int len  = len = sizeof(req->sin);
	int res;
	memset(&resp, 0, sizeof(resp));

		//struct megaco_users *p = sub->parent;
	char v[256];
	char *h;
	int i=0;
	snprintf(v, sizeof(v),"[%s]:2944 ",  megacomg->addr.sin_addr.s_addr ? ast_inet_ntoa(megacomg->addr.sin_addr) : ast_inet_ntoa(megacomg->defaddr.sin_addr));

	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);//req->transactionIDtext);
	add_header(&resp, "C=", req->contextId);
	add_header(&resp, "MF=", req->notifyId);
	add_header_n1(&resp, "SG{SL=1234{an/apf{an=2}}},E=1001 {g/sc}", "}");
	add_header_n1(&resp, "}", "}");

	if (mgcpdebug)
		ast_verb(3," Modify play announce will be: %s \n",resp.data);
	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&req->sin), len);


	return 0;

}
static int transmit_ModifyCongestionTone(struct megaco_request *req,struct megaco_subchannel *sub)
{
	struct megaco_request resp;
	int len  = len = sizeof(req->sin);
	int res;
	memset(&resp, 0, sizeof(resp));

		//struct megaco_users *p = sub->parent;
	char v[256];
	char *h;
	int i=0;
	snprintf(v, sizeof(v),"[%s]:2944 ",  megacomg->addr.sin_addr.s_addr ? ast_inet_ntoa(megacomg->addr.sin_addr) : ast_inet_ntoa(megacomg->defaddr.sin_addr));

	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);//req->transactionIDtext);
	add_header(&resp, "C=", req->contextId);
	add_header(&resp, "MF=", req->notifyId);
	add_header_n1(&resp, "SG{cg/ct}", "}");
	add_header_n1(&resp, "}", "}");

	if (mgcpdebug)
		ast_verb(3," Modify Congestion Tone  will be: %s \n",resp.data);
	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&req->sin), len);


	return 0;
}
static int transmit_ModifySpecialInformationTone(struct megaco_request *req,struct megaco_subchannel *sub)
{
	struct megaco_request resp;
	int len  = len = sizeof(req->sin);
	int res;
	memset(&resp, 0, sizeof(resp));

		//struct megaco_users *p = sub->parent;
	char v[256];
	char *h;
	int i=0;
	snprintf(v, sizeof(v),"[%s]:2944 ",  megacomg->addr.sin_addr.s_addr ? ast_inet_ntoa(megacomg->addr.sin_addr) : ast_inet_ntoa(megacomg->defaddr.sin_addr));

	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);//req->transactionIDtext);
	add_header(&resp, "C=", req->contextId);
	add_header(&resp, "MF=", req->notifyId);
	add_header_n1(&resp, "SG{cg/sit}", "}");
	add_header_n1(&resp, "}", "}");

	if (mgcpdebug)
		ast_verb(3," Modify Special Information Tone  will be: %s \n",resp.data);
	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&req->sin), len);


	return 0;
}
static int transmit_ModifyPayPhoneRinginigTone(struct megaco_request *req,struct megaco_subchannel *sub)
{

	struct megaco_request resp;
	int len  = len = sizeof(req->sin);
	int res;
	memset(&resp, 0, sizeof(resp));

		//struct megaco_users *p = sub->parent;
	char v[256];
	char *h;
	int i=0;
	snprintf(v, sizeof(v),"[%s]:2944 ",  megacomg->addr.sin_addr.s_addr ? ast_inet_ntoa(megacomg->addr.sin_addr) : ast_inet_ntoa(megacomg->defaddr.sin_addr));

	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);//req->transactionIDtext);
	add_header(&resp, "C=", req->contextId);
	add_header(&resp, "MF=", req->notifyId);
	add_header_n1(&resp, "SG{cg/prt}", "}");
	add_header_n1(&resp, "}", "}");

	if (mgcpdebug)
		ast_verb(3," Modify PayPhone Ringing Tone will be: %s \n",resp.data);
	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&req->sin), len);


	return 0;
}
static int transmit_ModifyWarningTone(struct megaco_request *req,struct megaco_subchannel *sub)
{
    struct megaco_request resp;
	int len  = len = sizeof(req->sin);
	int res;
	memset(&resp, 0, sizeof(resp));

		//struct megaco_users *p = sub->parent;
	char v[256];
	char *h;
	int i=0;
	snprintf(v, sizeof(v),"[%s]:2944 ",  megacomg->addr.sin_addr.s_addr ? ast_inet_ntoa(megacomg->addr.sin_addr) : ast_inet_ntoa(megacomg->defaddr.sin_addr));

	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);//req->transactionIDtext);
	add_header(&resp, "C=", req->contextId);
	add_header(&resp, "MF=", req->notifyId);
	add_header_n1(&resp, "SG{cg/wt}", "}");
	add_header_n1(&resp, "}", "}");

	if (mgcpdebug)
		ast_verb(3," Modify Warning Tone will be: %s \n",resp.data);
	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&req->sin), len);


	return 0;

}
static int transmit_ModifyCallerWaitingTone(struct megaco_request *req,struct megaco_subchannel *sub)
{
	struct megaco_request resp;
	int len  = len = sizeof(req->sin);
	int res;
	memset(&resp, 0, sizeof(resp));

		//struct megaco_users *p = sub->parent;
	char v[256];
	char *h;
	int i=0;
	snprintf(v, sizeof(v),"[%s]:2944 ",  megacomg->addr.sin_addr.s_addr ? ast_inet_ntoa(megacomg->addr.sin_addr) : ast_inet_ntoa(megacomg->defaddr.sin_addr));

	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);//req->transactionIDtext);
	add_header(&resp, "C=", req->contextId);
	add_header(&resp, "MF=", req->notifyId);

	add_header_n1(&resp, "SG{cg/cr}", "}");
	add_header_n1(&resp, "}", "}");

	if (mgcpdebug)
		ast_verb(3," Modify CallerWaitning Tone  will be: %s \n",resp.data);
	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&req->sin), len);


	return 0;


}

static int transmit_ModifyOffhookDialTone(struct megaco_request *req,struct megaco_subchannel *sub)
{
	struct megaco_request resp;
	int len  = len = sizeof(req->sin);
	int res;
	memset(&resp, 0, sizeof(resp));

	struct megaco_mg *mg = sub->parent->parent;


	char v[256];
	char ldmap[256];
	char *h;
	int i=0;
	snprintf(v, sizeof(v),"[%s]:2944 ", mg->domain);// mg->addr.sin_addr.s_addr ? ast_inet_ntoa(mg->addr.sin_addr) : ast_inet_ntoa(mg->defaddr.sin_addr));

	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);
	add_header(&resp, "C=", req->contextId);
	add_header(&resp, "MF=", req->notifyId);
	add_header(&resp, "E=", "2223");

	snprintf(ldmap,sizeof(ldmap),"al/*,dd/ce{DigitMap = dmap1}},SG{cg/dt},DM = dmap1 {%s}",mg->dmap);
	//snprintf(ldmap,sizeof(ldmap),"dd/ce{DM=dmap1},al/*},SG{cg/dt},DM=dmap1{%s}","([2-8]xx|00xxxxxxxxx|0[1-8]xxxxx|09[13]xxx|09[024-9]xx|9xxxx|17|1[0-9]x|E|x.E|F|x.F|x.L)");//mg->dmap);
	//snprintf(ldmap,sizeof(ldmap),"dd/ce{DM=dmap1},al/*},SG{cg/dt},DM=dmap1{([2-8]xxx|00xxxxxxxxx|0[1-8]xxxxx|09[13]xxx|09[024-9]xx|4xx|17|1[0-9]x|E|x.E|F|x.F|x.L)}");
	add_header_n1(&resp, ldmap, "}");


	add_header_n1(&resp, "}", "}");

	if (mgcpdebug)
		ast_verb(3," ModifyOffhookDialTone will be: %s \n",resp.data);
	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&req->sin), len);
    // MG Add for retransmitting
	//megaco_postrequest(sub->parent,sub, resp.data,resp.len, 0);
	return 0;

}

static int transmit_MgCheckAlliveMGC(struct megaco_subchannel *sub)
{
	struct megaco_request resp;
	int res;
	memset(&resp, 0, sizeof(resp));

	struct megaco_mg *mg = sub->parent->parent;
	int len  = sizeof(mg->addr);

	char v[256];
	char ldmap[256];

	snprintf(v, sizeof(v),"[%s]:2944 ", mg->domain);// mg->addr.sin_addr.s_addr ? ast_inet_ntoa(mg->addr.sin_addr) : ast_inet_ntoa(mg->defaddr.sin_addr));

	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);
	add_header(&resp, "C=", "-");
	add_header_n1(&resp, "N=","ROOT{OE=0{20150415T04523901:it/ito}}");


	add_header_n1(&resp, "}", "}");

	if (mgcpdebug)
		ast_verb(3," MgCheckAlliveMGC will be: %s \n",resp.data);

	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&mg->addr), len);
    //MG Add for
	//megaco_postrequest(sub->parent,sub, resp.data,resp.len, 0);
	return 0;

}


static int transmit_ModifyToChekOffhook(struct megaco_request *req,char *contextId,char *modifyId,struct megaco_subchannel *sub)
{
	struct megaco_request resp;
	int res;
	memset(&resp, 0, sizeof(resp));

	struct megaco_mg *mg = sub->parent->parent;
	int len  = sizeof(mg->addr);
	char v[256];

	snprintf(v, sizeof(v),"[%s]:2944 ", mg->domain);// megacomg->addr.sin_addr.s_addr ? ast_inet_ntoa(megacomg->addr.sin_addr) : ast_inet_ntoa(megacomg->defaddr.sin_addr));

	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);//req->transactionIDtext);
	add_header(&resp, "C=", contextId);
	add_header(&resp, "MF=", modifyId);
	add_header(&resp, "E=", "2222");
	add_header_n1(&resp, "al/*},SG{}", "}");
	add_header_n1(&resp, "}", "}");

	if (mgcpdebug)
		ast_verb(3," ModifyToChekOffhook will be: /%s/ \n",resp.data);
	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&mg->addr), len);


	return 0;
}

static int transmit_SubtractAllContext(struct megaco_request *req,char *contextId,struct megaco_subchannel *sub)
{
	struct megaco_request resp;

	int res;
	memset(&resp, 0, sizeof(resp));

    struct megaco_mg *mg = sub->parent->parent;
	int len   = sizeof(mg->addr);
	char v[256];
	char *h;
	int i=0;
	snprintf(v, sizeof(v),"[%s]:2944 ", mg->domain);

	add_header_n1(&resp, "!/1 ", v);
	add_header_i(&resp, "T=", megaco_req_id++);
	add_header(&resp, "C=", contextId);
	add_header_n1(&resp, "S=*", "");

	add_header_n1(&resp, "}", "}");

	if (mgcpdebug)
		ast_verb(3," SubtractAllContext  will be:%s \n",resp.data);
	res = sendto(mgcpsock, resp.data,resp.len, 0, (struct sockaddr*) (&mg->addr), len);


	return 0;
}



static int transmit_modify_request(struct megaco_subchannel *sub)
{
	struct megaco_request resp;
	struct megaco_users *p = sub->parent;
	struct ast_format tmpfmt;
	int fc = 1;
	char local[256];
	char tmp[80];

		return 0;
}


static void add_header_offhook(struct megaco_subchannel *sub, struct megaco_request *resp, char *tone)
{
	struct megaco_users *p = sub->parent;
	char tone_indicate_end = 0;

}




static int transmit_audit_endpoint(struct megaco_users *p)
{
	struct  resp;

	return 0;
}

static int transmit_connection_del(struct megaco_subchannel *sub)
{
	struct megaco_users *p = sub->parent;
	struct megaco_request resp;


	return 0;
}

static int transmit_connection_del_w_params(struct megaco_users *p, char *callid, char *cxident)
{
	struct megaco_request resp;


	return 0;
}

/*! \brief  dump_cmd_queues: (SC:) cleanup pending commands */
static void dump_cmd_queues(struct megaco_users *p, struct megaco_subchannel *sub)
{
	struct megaco_request *t, *q;


}


/*! \brief  find_command: (SC:) remove command transaction from queue */
static struct megaco_request *find_command(struct megaco_users *p, struct megaco_subchannel *sub,
		struct megaco_request **queue, ast_mutex_t *l, int ident)
{
	struct megaco_request *prev, *req;

		ast_mutex_lock(l);
		for (prev = NULL, req = *queue; req; prev = req, req = req->next) {
			if (req->trid == ident) {
				/* remove from queue */
				if (!prev)
					*queue = req->next;
				else
					prev->next = req->next;

				/* send next pending command */
				if (*queue) {
					ast_debug(1, "Posting Queued Request:\n%s to %s:%d\n", (*queue)->data,
						ast_inet_ntoa(p->parent->addr.sin_addr), ntohs(p->parent->addr.sin_port));

					//mgcp_postrequest(p, sub, (*queue)->data, (*queue)->len, (*queue)->trid);???????????
				}
				break;
			}
		}
		ast_mutex_unlock(l);
		return req;
}

static void megaco_start_rtp(struct megaco_subchannel *sub,struct ast_rtp_instance *rtp)
{
	struct ast_sockaddr bindaddr_tmp;
    ast_verb(3,"--------------------------Start_rtp \n");
	ast_mutex_lock(&sub->lock);
	/* check again to be on the safe side */
	/* Make sure previous RTP instances/FD's do not leak */
	if (sub->rtp) {
		ast_rtp_instance_destroy(sub->rtp);
		sub->rtp = NULL;
	}
	/* Allocate the RTP now */
	ast_sockaddr_from_sin(&bindaddr_tmp, &bindaddr);
	sub->rtp = ast_rtp_instance_new("phonix", sched, &bindaddr_tmp, NULL);

	if (sub->rtp && sub->owner){
		ast_channel_set_fd(sub->owner, 0, ast_rtp_instance_fd(sub->rtp, 0));
		//ast_verb(3,"HHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHHhhh\n");
	}
	if (sub->rtp) {
		ast_rtp_instance_set_qos(sub->rtp, qos.tos_audio, qos.cos_audio, "MEGACO RTP");
		ast_rtp_instance_set_prop(sub->rtp, AST_RTP_PROPERTY_NAT, sub->nat);
	}
	/* Make a call*ID */
	snprintf(sub->callid, sizeof(sub->callid), "%08lx%s", ast_random(), sub->txident);

	ast_mutex_unlock(&sub->lock);
}
#ifdef OMIT_FORTEST
static void *mgcp_ss(void *data)
{
	struct ast_channel *chan = data;
	struct megaco_subchannel *sub = ast_channel_tech_pvt(chan);
	struct megaco_users *p = sub->parent;
	/* char exten[AST_MAX_EXTENSION] = ""; */
	int len = 0;
	int timeout = firstdigittimeout;
	int res= 0;
	int getforward = 0;
	int loop_pause = 100;


	return NULL;
}

static int attempt_transfer(struct megaco_users *p)
{
	return 0 ;
}

static void handle_hd_hf(struct megaco_subchannel *sub, char *ev)
{
	struct megaco_users *p = sub->parent;
	struct ast_channel *c;

}

static int find_and_retrans(struct megaco_subchannel *sub, struct megaco_request *req)
{
	int seqno=0;
	time_t now;
	struct megaco_response *prev = NULL, *cur, *next, *answer = NULL;

	return 0;
}
#endif

static int mgcpsock_read(int *id, int fd, short events, void *ignore)
{
	struct megaco_request req;
	//struct megaco_request send;
//	struct sockaddr_in sin;
	struct megaco_subchannel *sub;
	struct megaco_subchannel *sub_bparty;
	struct ast_channel *c;
	struct megaco_users *p ;
	int res,postdgt=0;
	socklen_t len;
    char ss[256];
	int result;
	int ident;
	int calltype,i=0;
    int  mg_type;
	
	
	len = sizeof(req.sin);
	memset(&req, 0, sizeof(req));
	res = recvfrom(mgcpsock, req.data, sizeof(req.data) - 1, 0, (struct sockaddr *)&(req.sin), &len);
	if (res < 0) {
		if (errno != ECONNREFUSED)
			ast_log(LOG_WARNING, "Recv error: %s\n", strerror(errno));
		return 1;
	}

	/*for (i=0; i<res; i++)
	{
		if (req.data[i] == '\n')
		{
			req.data[i] = ' ';break;
		}
	}*/

	req.data[res] = '\0';
	req.len = res;
	//memcpy(&send.len,&req.len,sizeof(req));

	if (mgcpdebug)
	{
		ast_verb(3, "<-- Megaco %d read -->: %s ...  from %s:%d\n",i, req.data, ast_inet_ntoa(req.sin.sin_addr), ntohs(req.sin.sin_port));
		//ast_verb(3, "<< %s\n",req.data);
     //   ast_verb(3, "Source IP&Port: %s:%d\n", ast_inet_ntoa(req.sin.sin_addr), ntohs(req.sin.sin_port));

	}
	snprintf(ss,sizeof(ss),"%s",ast_inet_ntoa(req.sin.sin_addr));
    mg_type= find_ag_type(ss);  
	megaco_parse(&req,mg_type);

	switch(req.transactionFlag)
	{
	  case 0:
		//reply megaco package recevied
		switch(req.cmd)
		{
		case  MEGACO_RSPACK:
			//transmit_ResponseAck(&req);
			break;
		case MEGACO_MODIFY:
			snprintf(ss,sizeof(ss),"%s",req.notifyId);
			sub = find_subchannel_and_lock(ss, ident, &req.sin);
			if(sub && (sub->parent->callstate==MG_AWAIT_INIT_OK_ST))
			{

				sub->parent->callstate = MEGACO_IDLE_ST;
				ast_verb(3,"Megaco :%s Goes IDLE \n",sub->parent->name);

			}
			break;

		case MEGACO_ADD:

		//	ast_verb(3,"-------------------AAAAA  Add reply received:<%s>",req.notifyId);
			snprintf(ss,sizeof(ss),"%s",req.notifyId);
			sub = find_subchannel_and_lock(ss, ident, &req.sin);
			if(sub)
			{
				switch(sub->parent->callstate)
				{
				case MEGACO_WFANSWER_ST:
					//tremination ID is Aparty
					memcpy(sub->parent->contextId,req.contextId,sizeof(sub->parent->contextId));
					memcpy(sub->parent->ephermalId,req.ephermalId,sizeof(sub->parent->ephermalId));
					memcpy(sub->parent->rtpLparam,req.rtpLparam,sizeof(sub->parent->rtpLparam));
					ast_verb(3,":::::::::::::::: Save Add context ID for <%s>:<%s> ephermalId:<%s>",req.notifyId,sub->parent->contextId,sub->parent->ephermalId);
					ast_verb(3,"rtpLParam <%s>\n",sub->parent->rtpLparam);
					transmit_ModifyRingBackTone(&req,sub);
					break;
				case MEGACO_RING_ST:
					//termination ID is Bparty
					memcpy(sub->parent->contextId,req.contextId,sizeof(sub->parent->contextId));
					memcpy(sub->parent->ephermalId,req.ephermalId,sizeof(sub->parent->ephermalId));
					memcpy(sub->parent->rtpLparam,req.rtpLparam,sizeof(sub->parent->rtpLparam));
					//ast_verb(3,":::::::::::::::::::Save Add context ID for <%s>:<%s> ephermalId:<%s>",req.notifyId,sub->parent->contextId,sub->parent->ephermalId);
					//ast_verb(3,"rtpLParam <%s>\n",sub->parent->rtpLparam);
					transmit_ModifyRing(&req,sub);
					break;
				case MEGACO_SIP_WFRINGACK_ST:
					//ast_verb(3,"MEGACO_SIP_WFRINGACK_ST    :%s %d \n",req.rtpLparam,req.lines);
				
					process_sdp(sub, &req);
					memcpy(sub->parent->contextId,req.contextId,sizeof(sub->parent->contextId));
					memcpy(sub->parent->ephermalId,req.ephermalId,sizeof(sub->parent->ephermalId));
					memcpy(sub->parent->rtpLparam,req.rtpLparam,sizeof(sub->parent->rtpLparam));
					//
					//ast_verb(3,":::::: SIP ::::::::Save Add context ID for <%s>:<%s> ephermalId:<%s>",req.notifyId,sub->parent->contextId,sub->parent->ephermalId);
					//ast_verb(3,"rtpLParam <%s>\n",sub->parent->rtpLparam);
					transmit_ModifyRing(&req,sub);
					//send ring for sip
					sub->parent->callstate = MEGACO_SIP_WFANSWER_ST;
					ast_queue_control(sub->owner, AST_CONTROL_RINGING); //for set to rquestor

					break;
				case MEGACO_MG_WFRINGACK_ST:
					//ast_verb(3,"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA:%s %d \n",req.rtpLparam,req.lines);
					megaco_start_rtp(sub,sub->rtp);
					process_sdp(sub, &req);
					memcpy(sub->parent->contextId,req.contextId,sizeof(sub->parent->contextId));
					memcpy(sub->parent->ephermalId,req.ephermalId,sizeof(sub->parent->ephermalId));
					memcpy(sub->parent->rtpLparam,req.rtpLparam,sizeof(sub->parent->rtpLparam));
					ast_verb(3,":::::: MG ::::::::Save Add context ID for <%s>:<%s> ephermalId:<%s>",req.notifyId,sub->parent->contextId,sub->parent->ephermalId);
					ast_verb(3,"rtpLParam <%s>\n",sub->parent->rtpLparam);

					p= sub->parent;
					//pbx must be start here
					snprintf(p->context,sizeof(p->context),"%s","phonix");
					snprintf(p->exten,sizeof(p->exten),"%s",p->destId);
					postdgt = atoi((p->name+1));
					//snprintf(p->cid_num,sizeof(p->cid_num),"%s%03d",p->parent->predgt,postdgt);//p->name+1);
					//snprintf(p->cid_num,sizeof(p->cid_num),"%s@%s",p->name,p->parent->name);
					snprintf(p->cid_num,sizeof(p->cid_num),"%s",p->telNo);
					
					


					c = megaco_new(sub, AST_STATE_RING, NULL,0);

					if (!c) {
						ast_log(LOG_WARNING, "????Unable to start PBX on channel %s@%s\n", p->name, p->parent->name);
						//ast_verb(3, "Unable to start PBX on channel %s@%s\n", p->name, p->parent->name);
						transmit_ModifyBusyTone(req.contextId,req.notifyId,sub);
						sub->parent->callstate=MEGACO_WFONHOOK_ST;
						ast_hangup(c);
						return 1;
					}
					ast_log(LOG_WARNING, "A Succesfully start PBX on channel %s@%s,State <%s> \n", p->name, p->parent->name,megacostate2str(sub->parent->callstate));

				//	transmit_ModifyRingBackTone(&req,sub);//CRBT



					break;
					default:

						ast_log(LOG_WARNING,"Add Reply state <%s@%s> Error:%d \n",p->name, p->parent->name,megacostate2str(sub->parent->callstate));
						break;
				}
			}




	/*		snprintf(ss,sizeof(ss),"%s",req.notifyId);
			sub = find_subchannel_and_lock(ss, ident, &req.sin);
			if(sub)
			{
				memcpy(sub->parent->contextId,req.contextId,sizeof(sub->parent->contextId));
				ast_verb(3,"Save Add context ID for <%s>:<%s> \n",req.notifyId,sub->parent->contextId);
				transmit_ModifyRingBackTone(&req,sub);

			}
			snprintf(ss,sizeof(ss),"%s",req.destId);
			sub_bparty = find_subchannel_and_lock(ss, ident, &req.sin);
			if(sub_bparty){
				memcpy(sub_bparty->parent->contextId,req.contextId,sizeof(sub_bparty->parent->contextId));
				ast_verb(3,"Save Add context ID for <%s>:<%s> \n",req.destId,sub_bparty->parent->contextId);
				transmit_ModifyRing(&req,sub_bparty);



			}

*/
			break;
		case MEGACO_ERROR:

			break;
		case MEGACO_SUBTRACT:

			break;
		case MEGACO_AUDIT:
			snprintf(ss,sizeof(ss),"%s",req.notifyId);
			sub = find_subchannel_and_lock(ss, ident, &req.sin);
			if(sub )
			{
				sub->AuditRetansCount =0 ;
				sub->parent->callstate = MG_ALLIVE_ST;
				ast_verb(3,"---mkm  Megaco Audit reply :%d\n",sub->AuditRetansCount);
			}
			else
				ast_verb(3,"Megaco Audit reply :%s  not Found\n",req.notifyId);	
			break;
		default:
			ast_verb(3,"Megaco reply cmd unkown:%d \n",req.cmd);
			break;
		}
		break;
	case 1:
		//Transaction megaco packge received
		switch(req.cmd)
		{
			case MEGACO_NOTIFY:
				//ast_verb(3,"??????????   notify command received:<%s> \n",req.notifyId);
				snprintf(ss,sizeof(ss),"%s",req.notifyId);
				sub = find_subchannel_and_lock(ss, ident, &req.sin);
				if(!sub)
				{
					ast_log(LOG_WARNING, "Unable to find termination <%s> \n",ss);
					return 1;
				}

				transmit_notify_resp(&req,sub);
				switch(req.al_event)
				{
				
					case MEGACO_OFFHOOK_EV:
					    ast_log(LOG_WARNING,"MEGACO OFFHOOK received :%s State:%s destId:%s ContextId:%s\n",req.notifyId,megacostate2str(sub->parent->callstate),sub->parent->destId,req.contextId);

						if(sub)
						{
							switch(sub->parent->callstate)
							{
								case MEGACO_IDLE_ST:
									transmit_ModifyOffhookDialTone(&req,sub);
									sub->parent->falshcnt = 0;
									sub->parent->callstate =MEGACO_WFDIGIT_ST;
									memset(sub->parent->destId,0,sizeof(sub->parent->destId));
									sub->parent->iscallwaiting =0;
								break;
								case MEGACO_RING_ST:
										sub->parent->callstate =MEGACO_ANSWER_ST;
										snprintf(ss,sizeof(ss),"%s",sub->parent->destId);
										sub_bparty = find_subchannel_and_lock(ss, ident, &sub->parent->destIp_addr);
										//must check add for if(sub_bparty)
										sub_bparty->parent->callstate =MEGACO_ANSWER_ST;
										ast_verb(3,"------------    Bparty answered aparty<%s>:<%s> Bparty<%s>:<%s>\n",sub->parent->destId,sub_bparty->parent->contextId,req.notifyId,sub->parent->contextId);

										transmit_ModifyTdmNoSignalWithSDP(&req,sub->parent->contextId,req.notifyId,sub,sub_bparty);
										transmit_ModifyTdmNoSignalWithSDP(&req,sub_bparty->parent->contextId,sub->parent->destId,sub_bparty,sub);
								//		transmit_connectAB(&req,sub->parent->destId,sub_bparty->parent->contextId,req.notifyId,sub->parent->contextId);
										//transmit_connectAB(&req,req.notifyId,sub->parent->contextId,sub->parent->destId,sub_bparty->parent->contextId);

								break;
								case MEGACO_SIP_WFANSWER_ST:
									sub->parent->callstate =MEGACO_SIP_ANSWER_ST;
									//transmit_ModifyTdmNoSignalWithSDP(&req,req.contextId,req.notifyId,sub,NULL); //omit here and in megco_indicate

									ast_verb(3,"------------    Bparty answered aparty<%s>:<%s> Bparty<%s>:<%s>\n",sub->parent->destId,sub->parent->contextId,req.notifyId,sub->parent->contextId);
									//SIP endpoint must be answerd
									ast_queue_control(sub->owner, AST_CONTROL_ANSWER); //for set to rquestor

									break;
							default:
									ast_verb(3,"Notify offhook Event state error:%s\n",megacostate2str( sub->parent->callstate));
									transmit_ModifyBusyTone(req.contextId,req.notifyId,sub);
									sub->parent->callstate =MEGACO_IDLE_ST;
								break;
							}
						}
					break;
				case MEGACO_ONHOOK_EV:

					ast_log(LOG_WARNING,"MEGACO ONHOOK received :%s State:%s destId:%s ContextId:%s\n",req.notifyId,megacostate2str(sub->parent->callstate),sub->parent->destId,req.contextId);

					if(sub)
					{
						switch(sub->parent->callstate)
						{
							 case 	MEGACO_MG_WFANSWER_ST:
							 case   MEGACO_SIP_HOLD_ST:
								/* //ast_verb(3,"-------eeeeeeeeee2\n");
								 transmit_SubtractAllContext(&req,sub->parent->contextId,sub);
								// usleep(2000);
								 //memset(req.contextId,0,sizeof(req.contextId));

								 req.contextId[0]='-';
								 transmit_ModifyToChekOffhook(&req,req.contextId,req.notifyId,sub);*/
								transmit_ModifyTdmNoSignal(&req,req.contextId,req.notifyId,sub);

								usleep(1000);
								if( strcmp(req.contextId,"-"))
									transmit_SubtractAllContext(&req,req.contextId,sub);  //keymile add							 
								 sub->parent->callstate = MEGACO_IDLE_ST;
								
                                 //add check if is call waiting active
								 ast_queue_control(sub->owner, AST_CONTROL_HANGUP);


							return 1;

							case MEGACO_ANSWER_ST:
							case MEGACO_WFANSWER_ST:
							case  MEGACO_MG_WFRINGACK_ST:
							
								 
								 transmit_SubtractAllContext(&req,sub->parent->contextId,sub);
								 memset(req.contextId,0,sizeof(req.contextId));
								 usleep(1000);
								 req.contextId[0]='-';
								 transmit_ModifyToChekOffhook(&req,req.contextId,req.notifyId,sub);
								 sub->parent->callstate = MEGACO_IDLE_ST;

								break;
							case MEGACO_WFDIGIT_ST:
							case MEGACO_WFONHOOK_ST:

								transmit_ModifyTdmNoSignal(&req,req.contextId,req.notifyId,sub);

								usleep(1000);
								if( strcmp(req.contextId,"-"))
									transmit_SubtractAllContext(&req,req.contextId,sub);  //keymile add
								sub->parent->callstate = MEGACO_IDLE_ST;
								return 1;
							case	MEGACO_MG_ANSWER_ST:
							case	MEGACO_SIP_ANSWER_ST:
							case	MEGACO_SIP_WFANSWER_ST:
								


								transmit_ModifyTdmNoSignal(&req,req.contextId,req.notifyId,sub);

								usleep(1000);
								if( strcmp(req.contextId,"-"))
									transmit_SubtractAllContext(&req,req.contextId,sub);  //keymile add


								 sub->parent->callstate = MEGACO_IDLE_ST;

								 ast_queue_control(sub->owner, AST_CONTROL_HANGUP);
								//comment by mkmtest960420
								/* if(sub->parent->iscallwaiting ==1)
								 {
								    	ast_verb(3,"sub->parent->iscallwaiting:%d \n",sub->parent->iscallwaiting);
								    	if(sub->owner_hold)
								 			ast_queue_control(sub->owner_hold, AST_CONTROL_HANGUP);
								 		sub->parent->iscallwaiting =0;
								}*/
								 //comment by mkmtest960420
								
								break;
							default:
								ast_log(LOG_WARNING,"unknown call stat:%s %d \n",req.notifyId,sub->parent->callstate);
								break;
						}

						if(sub->parent->destId)
						{
							snprintf(ss,sizeof(ss),"%s",sub->parent->destId);
							sub_bparty = find_subchannel_and_lock(ss, ident, &req.sin);
							if(sub_bparty)
							{
								switch(sub_bparty->parent->callstate)
								{
									case MEGACO_ANSWER_ST:
									case MEGACO_RING_ST:
										transmit_SubtractAllContext(&req,sub_bparty->parent->contextId,sub_bparty);
										transmit_ModifyToChekOffhook(&req,req.contextId,sub->parent->destId,sub_bparty);
										sub_bparty->parent->callstate = MEGACO_IDLE_ST;

										break;
									default:
										break;
								}

							}
						}
						/*
						if((sub->parent->callstate == )
							 transmit_SubtractAllContext
						else
							transmit_ModifyTdmNoSignal(&req,req.contextId,req.notifyId);


						if(sub->parent->destId)
						{
							snprintf(ss,sizeof(ss),"%s@fiberhome1",sub->parent->destId);
							sub_bparty = find_subchannel_and_lock(ss, ident, &req.sin);
							if(sub_bparty)
							{
								sub_bparty->parent->callstate = MEGACO_IDLE_ST;
								transmit_ModifyTdmNoSignal(&req,sub_bparty->parent->contextId,sub->parent->destId);
							}


						}*/
					}

				break;
				case MEGACO_ALLIVECHECK_EV:
					//ast_verb(3,"-----------------megaco allive check received \n");
					break;

				case MEGACO_DIALDIGIT_EV:
					sub->parent->calltype = MEGACO_INVALID_CALL_TYPE;
					//ast_verb(3, "<--2 Megaco------------------::::from %s:%d\n", ast_inet_ntoa(req.sin.sin_addr), ntohs(req.sin.sin_port));
					calltype = digit_analyze(&req,sub);
					//ast_verb(3,"MMMMMMMMegaco  Call type = :%d\n",calltype);
					switch(calltype)
					{
						case  MEGACO_LOCAL_CALL_TYPE:
							//it means call is inside of one mg
							sub->parent->calltype = MEGACO_LOCAL_CALL_TYPE;
							snprintf(ss,sizeof(ss),"%s",req.destId);
							sub_bparty = find_subchannel_and_lock(ss, ident, &sub->parent->destIp_addr);
							if(!sub_bparty)
							{
								ast_verb(3,"Megaco  bparty not founed :%s\n",ss);
								transmit_ModifyBusyTone(req.contextId,req.notifyId,sub);
								sub->parent->callstate=MEGACO_WFONHOOK_ST;
								//transmit_ModifyCallWaitingTone(&req);
								//transmit_ModifyPlayAnnouncment(&req);
								return 1;

							}
							// transmit_AddChooseOutgoing(&req,req.destId,sub); local tdm ok

							transmit_AddSipChooseOutgoing(&req,req.notifyId,sub);
							transmit_AddSipChooseOutgoing(&req,req.destId,sub_bparty);

							//bparty handle
		//					transmit_ModifyRing(&req);
							//save bparty first in aparty sub
							memcpy(sub->parent->destId,req.destId,sizeof(sub->parent->destId));
							ast_verb(3,"save Bparty id to <%s>:<%s>\n",req.notifyId,sub->parent->destId);
							sub->parent->callstate = MEGACO_WFANSWER_ST;
							//
							if(sub_bparty){
								sub_bparty->parent->callstate = MEGACO_RING_ST;
								memcpy(sub_bparty->parent->destId,req.notifyId,sizeof(sub_bparty->parent->destId));
								memcpy(&sub_bparty->parent->destIp_addr, &req.sin, sizeof(sub_bparty->parent->destIp_addr));
								ast_verb(3,"save Aparty id to <%s>:<%s>\n",req.destId,sub_bparty->parent->destId);
							}


							break;
						case  MEGACO_EXTERNAL_CALL_TYPE:
							//it means call is inside of TWO mg

							sub->parent->calltype = MEGACO_EXTERNAL_CALL_TYPE;
							snprintf(ss,sizeof(ss),"%s",req.destId);
							sub_bparty = find_subchannel_and_lock(ss, ident, &sub->parent->destIp_addr);
							if(!sub_bparty)
							{
								ast_verb(3,"Megaco bparty not founed :%s\n",ss);
								transmit_ModifyBusyTone(req.contextId,req.notifyId,sub);
								//transmit_ModifyCallWaitingTone(&req);
								//transmit_ModifyPlayAnnouncment(&req);
								return 1;

							}

							transmit_AddSipChooseOutgoing(&req,req.notifyId,sub);
							transmit_AddSipChooseOutgoing(&req,req.destId,sub_bparty);
							//bparty handle

							memcpy(sub->parent->destId,req.destId,sizeof(sub->parent->destId));
							ast_verb(3,"save Bparty id to <%s>:<%s>\n",req.notifyId,sub->parent->destId);
							sub->parent->callstate = MEGACO_WFANSWER_ST;
														//
							if(sub_bparty)
							{
								sub_bparty->parent->callstate = MEGACO_RING_ST;
								memcpy(sub_bparty->parent->destId,req.notifyId,sizeof(sub_bparty->parent->destId));
								memcpy(&sub_bparty->parent->destIp_addr, &req.sin, sizeof(sub_bparty->parent->destIp_addr));

								ast_verb(3,"save Aparty id to <%s>:<%s>\n",req.destId,sub_bparty->parent->destId);
							}
							break;
						case  MEGACO_NATIONAL_CALL_TYPE:
							ast_verb(3,"MEGACO_NATIONAL_CALL_TYPE <%s>,<%s>\n",req.notifyId,sub->parent->destId);
							//it means call is go out from mg with sip
							//it means call is inside of one mg
							sub->parent->calltype = MEGACO_NATIONAL_CALL_TYPE;

							transmit_AddSipChooseOutgoing(&req,req.notifyId,sub);


							//bparty handle
							//save bparty first in aparty sub
							memcpy(sub->parent->destId,req.destId,sizeof(sub->parent->destId));
							ast_verb(3,"save Bparty id to <%s>:<%s>\n",req.notifyId,sub->parent->destId);
							sub->parent->callstate = MEGACO_MG_WFRINGACK_ST;



							break;
					case MEGACO_INVALID_CALL_TYPE:		
					default:
							ast_verb(3,"Invalid Megaco call type :%d\n",calltype);
							ast_log(LOG_WARNING,"Invalid Megaco call type :%d\n",calltype);
							transmit_ModifyBusyTone(req.contextId,req.notifyId,sub);
							sub->parent->callstate=MEGACO_WFONHOOK_ST;
							return 1;							

					}
					break;
				case MEGACO_FLASHDETECT_EV:
						ast_log(LOG_WARNING,"MEGACO FLASH_HOOK received :%s State:%s destId:%s ContextId:%s\n",req.notifyId,megacostate2str(sub->parent->callstate),sub->parent->destId,req.contextId);				
				     	switch(sub->parent->callstate)
				     	{
				     	   //AST_CONTROL_FLASH
				     		
				     		case MEGACO_SIP_ANSWER_ST:
					     		//comment by mkmtest960420
					     		/*switch(sub->parent->falshcnt)
					     		{
					     				case 0:
											ast_verb(3,"1 >falsh detected------------------\n");
								       	    ast_queue_control(sub->owner,AST_CONTROL_HOLD);
	      					     		   	
						    	     		 if(sub->parent->iscallwaiting==1)
						        					ast_queue_control(sub->owner_hold, AST_CONTROL_ANSWER);	
						        				sub->parent->falshcnt++;				     				
					     				break;
					     				case 1:
	 											ast_verb(3,"2 > falsh detected------------------\n");
							    
							    				ast_queue_control(sub->owner,AST_CONTROL_UNHOLD);
	      					     		   	
						    	    			if(sub->parent->iscallwaiting==1)
						        				ast_queue_control(sub->owner_hold, AST_CONTROL_HOLD);
	 
						        				sub->parent->falshcnt++;				     				
					     				break;
					     				case 2:
	 											ast_verb(3,"3 > falsh detected------------------\n");
							    
							    				ast_queue_control(sub->owner,AST_CONTROL_HOLD);
	      					     		   	
						    	    			if(sub->parent->iscallwaiting==1)
						        				ast_queue_control(sub->owner_hold, AST_CONTROL_UNHOLD);
	 
						        				sub->parent->falshcnt--;				     				
					     				break;

					     				default:
					     				ast_verb(3,"Invalid Falsh cnt :%d \n ",sub->parent->falshcnt);
					     				break;


					     		}*///comment by mkmtest960420

                            break; 


				     


				     		  /*test for hold waiting music test
				     		  if(sub->parent->iscallwaiting ==0 )
				     		  {
				     		   	ast_queue_control(sub->owner,AST_CONTROL_HOLD);
				     		   	transmit_ModifyTdmNoSignalWithSDP_2(NULL,sub->parent->contextId,sub->parent->name,sub,NULL); 
				     		   	sub->parent->iscallwaiting = 1;
				     		  }
				     		  else
				     		  {
				     		  	ast_queue_control(sub->owner,AST_CONTROL_UNHOLD);
				     		  	transmit_ModifyTdmNoSignalWithSDP_1(NULL,sub->parent->contextId,sub->parent->name,sub,NULL); 
				     		  	sub->parent->iscallwaiting =0;
				     		  }

				     		  break;*/

					     /*case MEGACO_CALL_WAITING_ST:
					        ast_verb(3,"1falsh detected------------------\n");
										        
					       // transmit_ModifyOffhookDialTone(&req,sub);  ommit incase of call wating  
					        ast_queue_control(sub->owner,AST_CONTROL_HOLD);
      		     		   	
					        if(sub->parent->iscallwaiting==1)
					        	ast_queue_control(sub->owner_hold, AST_CONTROL_ANSWER);
				        
					        sub->parent->callstate = MEGACO_SIP_HOLD_ST;

					        break;*/

					     default:
					             ast_verb(3, ">>>>>flash on Unkonown State:%d \n",sub->parent->callstate); 
					        break;
					    }
					break;
				default:
					ast_verb(3,"??????Unknown megaco event :%d\n",req.al_event);
					break;
				}

				break;
			case MEGACO_SERVICECHANGE:
				snprintf(ss,sizeof(ss),"%s",req.servicechangeId);
				sub = find_subchannel_and_lock(ss, ident, &req.sin);

				ast_verb(3,"-----------MEGACO_SERVICECHANGE comand recived :<%s>\n",req.servicechangeId);
                if(sub)
                {
						if(!strcasecmp(req.servicechangeId,"root")) 
						{
							transmit_serviceChangeReply(&req,0,sub);
							sleep(1);
							ast_verb(3,"Send modify to all termination ID\n");
							//transmit_InitailAllTermination(&req,&req.sin);  //commnet for huawei mazandaran
							//transmit_MgAuditRoot(sub);  //comment for huawei mazandaran
							sub->AuditRetansCount =0;
							//transmit_ModifyAll(&req,"-","*");
							
						}
						else
						{
						    
							transmit_serviceChangeReply(&req,0,sub);
						    usleep(2000);
							ast_verb(3,"Send modify to termination ID:%s\n",req.servicechangeId);
							transmit_ModifyToChekOffhook(&req,req.contextId,req.servicechangeId,sub);						
						}
				}
				else
				{
					ast_verb(3,"termination ID :%s Not Found\n" ,req.servicechangeId);
				}

				/*if(strcmp(sub->parent->parent->name,"HuaweiUA500-1"))
                {
					//req.servicechangeId
					if(sub)
					{
						transmit_ModifyToChekOffhook(&req,req.contextId,req.servicechangeId,sub);
					}
               }*/

				break;
/*			case MEGACO_SERVICECHANGE_WITHK:

				ast_verb(3,"MEGACO_SERVICECHANGE_WITHK comand recived :<%s>\n",req.servicechangeId);
				transmit_serviceChangeReply(&req,1);


				break;*/
			default:
				ast_verb(3,"??????????   unrecognized command received\n");
				break;
		}

		break;
		default:
			//uhnadeled package received
			break;

	}

	return 1;
}

//
//static int buildServiceChangeReply(char *h,unsigned int transactionId, char *terminationId, char *contextId)
//{
//	char header[256];
//	int len=0;
//    memset(header,0,sizeof(header));
//	len =sprintf(h,"!/3 [192.168.1.20]:2944 \nReply=%d {Context=%s {ServiceChange=%s}}\n",transactionId, terminationId,contextId);
//
//    //std::string  addrstr = "[10.1.2.50]:2944";
//	//ast_copy_string(h ,header, sizeof(header));
//	ast_debug(1, "buildServiceChangeReply\n %s \n",header);
//
//  /*std::stringstream ss;
//  ss << "!/1 " << mgcMessageHeader << " P=" << transactionId << "{"
//     << "C=" << contextId << "{"
//     << "SC=" << terminationId << "}}\n";*/
//  return len;
//}



static int *mgcpsock_read_id = NULL;

static int mgcp_prune_realtime_gateway(struct megaco_mg *g)
{
	/*struct megaco_users *enext, *e;
	struct megaco_subchannel *s, *sub;
	int i, prune = 1;

	return prune;*/return 1;
}

static void *do_monitor(void *data)
{
	int res;
	int reloading;
	struct megaco_mg *g, *gprev;
	/*struct megaco_mg *g;*/
	/*struct megaco_users *e;*/
	/*time_t thispass = 0, lastpass = 0;*/
	time_t lastrun = 0;

	/* Add an I/O event to our UDP socket */
	if (mgcpsock > -1) {
		mgcpsock_read_id = ast_io_add(io, mgcpsock, mgcpsock_read, AST_IO_IN, NULL);
	}
	/* This thread monitors all the frame relay interfaces which are not yet in use
	   (and thus do not have a separate thread) indefinitely */
	/* From here on out, we die whenever asked */
	for (;;) {
		/* Check for a reload request */
		ast_mutex_lock(&mgcp_reload_lock);
		reloading = mgcp_reloading;
		mgcp_reloading = 0;
		ast_mutex_unlock(&mgcp_reload_lock);
		if (reloading) {
			ast_verb(1, "Reloading MEGACO v1.31\n");
			reload_config(1);
			/* Add an I/O event to our UDP socket */
			if (mgcpsock > -1 && !mgcpsock_read_id) {
				mgcpsock_read_id = ast_io_add(io, mgcpsock, mgcpsock_read, AST_IO_IN, NULL);
			}
		}

		/* Check for interfaces needing to be killed */
		/* Don't let anybody kill us right away.  Nobody should lock the interface list
		   and wait for the monitor list, but the other way around is okay. */
		ast_mutex_lock(&monlock);
		/* Lock the network interface */
		ast_mutex_lock(&netlock);


		/* pruning unused realtime megacomg, running in every 60 seconds*/
		if(time(NULL) > (lastrun + 60)) {
			ast_mutex_lock(&gatelock);
			g = megacomg;
			gprev = NULL;
			while(g) {
				if(g->realtime) {
					if(mgcp_prune_realtime_gateway(g)) {
						if(gprev) {
							gprev->next = g->next;
						} else {
							megacomg = g->next;
						}
						ast_mutex_unlock(&g->msgs_lock);
						ast_mutex_destroy(&g->msgs_lock);
						free(g);
					} else {
						ast_mutex_unlock(&g->msgs_lock);
						gprev = g;
					}
				} else {
					gprev = g;
				}
				g = g->next;
			}
			ast_mutex_unlock(&gatelock);
			lastrun = time(NULL);
		}
		/* Okay, now that we know what to do, release the network lock */
		ast_mutex_unlock(&netlock);
		/* And from now on, we're okay to be killed, so release the monitor lock as well */
		ast_mutex_unlock(&monlock);
		pthread_testcancel();
		/* Wait for sched or io */
		res = ast_sched_wait(sched);
		/* copied from chan_sip.c */
		if ((res < 0) || (res > 1000)) {
			res = 1000;
		}
		res = ast_io_wait(io, res);
		ast_mutex_lock(&monlock);
		if (res >= 0) {
			ast_sched_runq(sched);
		}
		ast_mutex_unlock(&monlock);
	}
	/* Never reached */
	return NULL;
}

static int restart_monitor(void)
{
	/* If we're supposed to be stopped -- stay stopped */
	if (monitor_thread == AST_PTHREADT_STOP)
		return 0;
	if (ast_mutex_lock(&monlock)) {
		ast_log(LOG_WARNING, "Unable to lock monitor\n");
		return -1;
	}
	if (monitor_thread == pthread_self()) {
		ast_mutex_unlock(&monlock);
		ast_log(LOG_WARNING, "Cannot kill myself\n");
		return -1;
	}
	if (monitor_thread != AST_PTHREADT_NULL) {
		/* Wake up the thread */
		pthread_kill(monitor_thread, SIGURG);
	} else {
		/* Start a new monitor */
		if (ast_pthread_create_background(&monitor_thread, NULL, do_monitor, NULL) < 0) {
			ast_mutex_unlock(&monlock);
			ast_log(LOG_ERROR, "Unable to start monitor thread.\n");
			return -1;
		}
	}
	ast_mutex_unlock(&monlock);
	return 0;
}

static struct ast_channel *megaco_request_call(const char *type, struct ast_format_cap *cap, const struct ast_channel *requestor, const char *dest, int *cause)
{
	struct megaco_subchannel *sub;
	struct ast_channel *tmpc = NULL;
	char tmp[256];int i=0;
	struct sockaddr_in sin;
	struct ast_party_connected_line connected;
	struct sip_pvt *p = ast_channel_tech_pvt(requestor);

	ast_log(LOG_WARNING,"megaco_request_call call form sip :%s %s\n",dest,type);
   

   
	if (!(ast_format_cap_has_joint(cap, global_capability))) {
		ast_log(LOG_NOTICE, "Asked to get a channel of unsupported format '%s'\n", ast_getformatname_multiple(tmp, sizeof(tmp), cap));
		/*return NULL;*/
	}


	ast_copy_string(tmp, dest, sizeof(tmp));
	if (ast_strlen_zero(tmp)) {
		ast_log(LOG_WARNING, "MEGACO Channels require an endpoint\n");
		*cause =AST_CAUSE_FAILURE;
		return NULL;
	}


	sip_find_mg_dest(tmp, &sin);


	if (!(sub = find_subchannel_and_lock(tmp, 0, &sin))) {
		ast_log(LOG_WARNING, "Ohh, Unable to find Megaco user '%s'\n", tmp);
		*cause = AST_CAUSE_UNREGISTERED;
		return NULL;
	}


	ast_log(LOG_WARNING, "---------megaco_request_call for --> (%s@%s) \n",sub->parent->name,sub->parent->parent->name);
	//ast_verb(3, "MGCP cw: %d, dnd: %d, so: %d, sno: %d\n",
		//	sub->parent->callwaiting, sub->parent->dnd, sub->owner ? 1 : 0, sub->next->owner ? 1: 0);
#ifdef FFFFFFOROLD
	/* Must be busy */
	if (((sub->parent->callwaiting) && ((sub->owner) && (sub->next->owner))) ||
		((!sub->parent->callwaiting) && (sub->owner)) ||
		 (sub->parent->dnd && (ast_strlen_zero(sub->parent->call_forward)))) {
		if (sub->parent->hookstate == MGCP_ONHOOK) {
			if (has_voicemail(sub->parent)) {
				transmit_notify_request(sub,"L/vmwi(+)");
			} else {
				transmit_notify_request(sub,"L/vmwi(-)");
			}
		}
		*cause = AST_CAUSE_BUSY;
		ast_mutex_unlock(&sub->lock);
		return NULL;
	}
#endif
	/* Must be busy */
	if(sub->owner)
	{
		ast_log(LOG_WARNING, "megaco_request_call--Ohh, User is busy now with owner '%s'\n", tmp);
		*cause = AST_CAUSE_BUSY;
		ast_mutex_unlock(&sub->lock);
		return NULL;
	}

    if((sub->parent->callstate!=MEGACO_IDLE_ST))//&&((sub->parent->callstate!=MEGACO_SIP_ANSWER_ST)))
    {
    	ast_log(LOG_WARNING, "--megaco_request_call --Dest is busy :%s state :%s \n",sub->parent->name,megacostate2str(sub->parent->callstate));
		*cause = AST_CAUSE_BUSY;
		ast_mutex_unlock(&sub->lock);
		return NULL;
    }


  /*  //lateradd for call waintg checking???????????????????????????????????????? 
     if(sub->parent->callstate == MEGACO_SIP_ANSWER_ST )  //check if user does not have callwaitnig send busy to aparty 
    {     

           ast_mutex_lock(&sub->lock);
           transmit_ModifyCallWaitingTone(sub->parent->contextId,sub->parent->name,sub);
           ast_mutex_unlock(&sub->lock);
    	   return ;
    }*/

	//	tmpc = megaco_new(sub->owner ? sub->next : sub, AST_STATE_DOWN, requestor ? ast_channel_linkedid(requestor) : NULL);
	//check for more that 1 call waitinig is ok or not  
	tmpc = megaco_new( sub, AST_STATE_DOWN, requestor ? ast_channel_linkedid(requestor) : NULL,1);
	

	if(sub->parent->callstate == MEGACO_IDLE_ST )
	 {
			if(!ast_strlen_zero(ast_channel_caller(requestor)->id.number.str))
				//&& ((p->callingpres & AST_PRES_RESTRICTION) == AST_PRES_ALLOWED))
			{
				memset(sub->callid, 0, sizeof(sub->callid));
				memset(sub->callid1, 0, sizeof(sub->callid1));
		    	snprintf(sub->callid, sizeof(sub->callid), "%s",ast_channel_caller(requestor)->id.number.str);// p->cid_num);
			sub->cid_len =0 ;	
		    	for(i=0;i<strlen(sub->callid);i++)
		    		if(sub->callid[i]!="")
		    		{
		    			sprintf(sub->callid1+strlen(sub->callid1), "3%c",sub->callid[i]);
					    sub->cid_byte[i] = toascii(sub->callid[i]);
					    sub->cid_len++;


		    		}
		    		else
		    			break;

		    	//ast_verb(3,"mkm add kermanshah  :%s callid len  is:%d callid1:%s  prese:%d\n",p->cid_num,strlen(sub->callid),sub->callid1,(p->callingpres & AST_PRES_RESTRICTION));


/*

                 int cid_len;
				 unsigned char cid_byte[32],sum,cid_checksum;

   
    			for(i=0;i<strlen(sub->callid1);i++)
			    {
    
			    	cid_byte[i] =sub->callid1[i];
    				sum +=	cid_byte[i];
			    }
   
     			cid_checksum = (~sum) +1   ;
			    cid_len  = i+8;  //8 becuaseof date-time 
				ast_verb(3,"CIDDDD   is :  %02x%02x%s%s%02x",4,cid_len,"3131313731303239",sub->callid1,cid_checksum);

*/




		    }
			else
			{
				snprintf(sub->callid1, sizeof(sub->callid1), "313030303030303031");
			}

			ast_verb(3,"SIP-Megaco request id.number:<Str:%s>form :%s -%s : %s-Recived\n",ast_channel_caller(requestor)->id.number.str,ast_channel_name(requestor),sub->parent->name,sub->callid1);
    		//ast_verb(3,"mkm add name:%s tttttttttttt  :%s callid len  is:%d callid1:%s  prese:%d\n",p->cid_name,p->cid_num,strlen(sub->callid),sub->callid1,(p->callingpres));

			if(tmpc)
			{
				//channel is created and  now ready for make call
				//OOOOOOOOO
				transmit_AddSipChooseOutgoing(NULL,tmp,sub);

				sub->parent->callstate = MEGACO_SIP_WFRINGACK_ST;

			}
  	 }
 /*  	else if(sub->parent->callstate == MEGACO_SIP_ANSWER_ST ) 
   {
   	       ast_mutex_lock(&sub->lock);
           transmit_ModifyCallWaitingTone(sub->parent->contextId,sub->parent->name,sub);
          // sub->parent->callstate = MEGACO_CALL_WAITING_ST;
           
   }*/

	ast_mutex_unlock(&sub->lock);
	if (!tmpc)
		ast_log(LOG_WARNING, "Unable to make channel for '%s'\n", tmp);
	else
		ast_verb(3, "------OK ---------make channel for '%s'\n", tmp);
	
	restart_monitor();

	return tmpc;
}

/* modified for reload support */
/*! \brief  build_gateway: parse mgcp.conf and create gateway/endpoint structures */
static struct megaco_mg *build_gateway(char *cat, struct ast_variable *v)
{
	struct megaco_mg *gw;
	struct megaco_users *e;
	struct megaco_subchannel *sub;
	struct ast_variable *chanvars = NULL;
    char *tmpc;
	/*char txident[80];*/
	int i=0, y=0;
	int gw_reload = 0;
	int ep_reload = 0;
	directmedia = DIRECTMEDIA;
	ast_verb(3,"------------------Build gateway -------------------------\n");
	/* locate existing gateway */
	for (gw = megacomg; gw; gw = gw->next) {
		if (!strcasecmp(cat, gw->name)) {
			/* gateway already exists */
			gw->delme = 0;
			gw_reload = 1;
			break;
		}
	}

	if (!gw && !(gw = ast_calloc(1, sizeof(*gw)))) {
		return NULL;
	}
	ast_verb(3,"1------------------Build gateway -------------------------:%d\n%s\n",gw_reload,cat);
	if (!gw_reload) {
		gw->expire = -1;
		gw->realtime = 0;
		gw->retransid = -1;
		ast_mutex_init(&gw->msgs_lock);
		ast_copy_string(gw->name, cat, sizeof(gw->name));


		/* check if the name is numeric ip */
		if ((strchr(gw->name, '.')) && inet_addr(gw->name) != INADDR_NONE)
			gw->isnamedottedip = 1;
	}
	for (; v; v = v->next) {
		if(!strcasecmp(v->name, "mg_model")){
		             ast_copy_string(mg_mode, v->value, sizeof(mg_mode));
		             ast_copy_string(gw->mg_mode, mg_mode, sizeof(gw->mg_mode));
		           }
		          else
		 if(!strcasecmp(v->name, "mg_version")){
             ast_copy_string(mg_version, v->value, sizeof(mg_version));
             ast_copy_string(gw->mg_version, mg_version, sizeof(gw->mg_version));
           }
          else
		 if(!strcasecmp(v->name, "dmap")){
					ast_copy_string(dmap, v->value, sizeof(dmap));
					ast_copy_string(gw->dmap, dmap, sizeof(gw->dmap));
		 }
		 else

		 if(!strcasecmp(v->name, "predgt")){
			 ast_copy_string(predgt, v->value, sizeof(predgt));
			 ast_copy_string(gw->predgt, predgt, sizeof(gw->predgt));
		 }
		else

		if(!strcasecmp(v->name, "domain"))
		{
			ast_copy_string(domain, v->value, sizeof(domain));
			ast_copy_string(gw->domain, domain, sizeof(gw->domain));
		}
		else
		  if (!strcasecmp(v->name, "host")) {
			if (!strcasecmp(v->value, "dynamic")) {
				/* They'll register with us */
				gw->dynamic = 1;
				memset(&gw->addr.sin_addr, 0, 4);
				if (gw->addr.sin_port) {
					/* If we've already got a port, make it the default rather than absolute */
					gw->defaddr.sin_port = gw->addr.sin_port;
					gw->addr.sin_port = 0;
				}
			} else {
				/* Non-dynamic.  Make sure we become that way if we're not */
				AST_SCHED_DEL(sched, gw->expire);
				gw->dynamic = 0;
				{
					struct ast_sockaddr tmp;

					ast_sockaddr_from_sin(&tmp, &gw->addr);
					if (ast_get_ip(&tmp, v->value)) {
						if (!gw_reload) {
							ast_mutex_destroy(&gw->msgs_lock);
							ast_free(gw);
						}
						return NULL;
					}
					ast_sockaddr_to_sin(&tmp, &gw->addr);
				}
			}
		} else if (!strcasecmp(v->name, "defaultip")) {
			struct ast_sockaddr tmp;

			ast_sockaddr_from_sin(&tmp, &gw->defaddr);
			if (ast_get_ip(&tmp, v->value)) {
				if (!gw_reload) {
					ast_mutex_destroy(&gw->msgs_lock);
					ast_free(gw);
				}
				return NULL;
			}
			ast_sockaddr_to_sin(&tmp, &gw->defaddr);
		} else if (!strcasecmp(v->name, "permit") ||
			!strcasecmp(v->name, "deny")) {
			gw->ha = ast_append_ha(v->name, v->value, gw->ha, NULL);
		} else if (!strcasecmp(v->name, "port")) {
			gw->addr.sin_port = htons(atoi(v->value));
		} else if (!strcasecmp(v->name, "context")) {
			ast_copy_string(context, v->value, sizeof(context));
		} else if (!strcasecmp(v->name, "dtmfmode")) {
			if (!strcasecmp(v->value, "inband"))
				dtmfmode = MGCP_DTMF_INBAND;
			else if (!strcasecmp(v->value, "rfc2833"))
				dtmfmode = MGCP_DTMF_RFC2833;
			else if (!strcasecmp(v->value, "hybrid"))
				dtmfmode = MGCP_DTMF_HYBRID;
			else if (!strcasecmp(v->value, "none"))
				dtmfmode = 0;
			else
				ast_log(LOG_WARNING, "'%s' is not a valid DTMF mode at line %d\n", v->value, v->lineno);
		} else if (!strcasecmp(v->name, "nat")) {
			nat = ast_true(v->value);
		} else if (!strcasecmp(v->name, "ncs")) {
			ncs = ast_true(v->value);
		} else if (!strcasecmp(v->name, "hangupongateremove")) {
			hangupongateremove = ast_true(v->value);
		} else if (!strcasecmp(v->name, "pktcgatealloc")) {
			pktcgatealloc = ast_true(v->value);
		} else if (!strcasecmp(v->name, "callerid")) {
			if (!strcasecmp(v->value, "asreceived")) {
				cid_num[0] = '\0';
				cid_name[0] = '\0';
			} else {
				ast_callerid_split(v->value, cid_name, sizeof(cid_name), cid_num, sizeof(cid_num));
			}
		} else if (!strcasecmp(v->name, "language")) {
			ast_copy_string(language, v->value, sizeof(language));
		} else if (!strcasecmp(v->name, "accountcode")) {
			ast_copy_string(accountcode, v->value, sizeof(accountcode));
		} else if (!strcasecmp(v->name, "amaflags")) {
			y = ast_cdr_amaflags2int(v->value);
			if (y < 0) {
				ast_log(LOG_WARNING, "Invalid AMA flags: %s at line %d\n", v->value, v->lineno);
			} else {
				amaflags = y;
			}
		} else if (!strcasecmp(v->name, "setvar")) {
			chanvars = add_var(v->value, chanvars);
		} else if (!strcasecmp(v->name, "clearvars")) {
			if (chanvars) {
				ast_variables_destroy(chanvars);
				chanvars = NULL;
			}
		} else if (!strcasecmp(v->name, "musiconhold")) {
			ast_copy_string(musicclass, v->value, sizeof(musicclass));
		} else if (!strcasecmp(v->name, "parkinglot")) {
			ast_copy_string(parkinglot, v->value, sizeof(parkinglot));
		} else if (!strcasecmp(v->name, "callgroup")) {
			cur_callergroup = ast_get_group(v->value);
		} else if (!strcasecmp(v->name, "pickupgroup")) {
			cur_pickupgroup = ast_get_group(v->value);
		} else if (!strcasecmp(v->name, "immediate")) {
			immediate = ast_true(v->value);
		} else if (!strcasecmp(v->name, "cancallforward")) {
			cancallforward = ast_true(v->value);
		} else if (!strcasecmp(v->name, "singlepath")) {
			singlepath = ast_true(v->value);
		} else if (!strcasecmp(v->name, "directmedia") || !strcasecmp(v->name, "canreinvite")) {
			directmedia = ast_true(v->value);
		} else if (!strcasecmp(v->name, "mailbox")) {
			ast_copy_string(mailbox, v->value, sizeof(mailbox));
		} else if (!strcasecmp(v->name, "hasvoicemail")) {
			if (ast_true(v->value) && ast_strlen_zero(mailbox)) {
				ast_copy_string(mailbox, gw->name, sizeof(mailbox));
			}
		} else if (!strcasecmp(v->name, "adsi")) {
			adsi = ast_true(v->value);
		} else if (!strcasecmp(v->name, "callreturn")) {
			callreturn = ast_true(v->value);
		} else if (!strcasecmp(v->name, "callwaiting")) {
			callwaiting = ast_true(v->value);
		} else if (!strcasecmp(v->name, "slowsequence")) {
			slowsequence = ast_true(v->value);
		} else if (!strcasecmp(v->name, "transfer")) {
			transfer = ast_true(v->value);
		} else if (!strcasecmp(v->name, "threewaycalling")) {
			threewaycalling = ast_true(v->value);
		} else if (!strcasecmp(v->name, "wcardep")) {
			/* locate existing endpoint */
			for (e = gw->endpoints; e; e = e->next) {
				if (!strcasecmp(v->value, e->name)) {
					/* endpoint already exists */
					e->delme = 0;
					ep_reload = 1;
					break;
				}
			}

			if (!e) {
				/* Allocate wildcard endpoint */
				e = ast_calloc(1, sizeof(*e));
				ep_reload = 0;
			}

			if (e) {
				if (!ep_reload) {
					memset(e, 0, sizeof(struct megaco_users));
					ast_mutex_init(&e->lock);
					ast_mutex_init(&e->rqnt_queue_lock);
					ast_mutex_init(&e->cmd_queue_lock);
					e->cap = ast_format_cap_alloc_nolock();
					ast_copy_string(e->name, v->value, sizeof(e->name));
					e->needaudit = 1;
				}
				e->callstate =  MEGACO_IDLE_ST;
				e->directmedia =1;
				ast_copy_string(gw->wcardep, v->value, sizeof(gw->wcardep));
				/* XXX Should we really check for uniqueness?? XXX */
				ast_copy_string(e->accountcode, accountcode, sizeof(e->accountcode));
				ast_copy_string(e->context, context, sizeof(e->context));
				ast_copy_string(e->cid_num, cid_num, sizeof(e->cid_num));
				ast_copy_string(e->cid_name, cid_name, sizeof(e->cid_name));
				ast_copy_string(e->language, language, sizeof(e->language));
				ast_copy_string(e->musicclass, musicclass, sizeof(e->musicclass));
				ast_copy_string(e->mailbox, mailbox, sizeof(e->mailbox));
				ast_copy_string(e->parkinglot, parkinglot, sizeof(e->parkinglot));
				if (!ast_strlen_zero(e->mailbox)) {
					char *mbox, *cntx;
					cntx = mbox = ast_strdupa(e->mailbox);
					strsep(&cntx, "@");
					if (ast_strlen_zero(cntx)) {
						cntx = "default";
					}
					e->mwi_event_sub = ast_event_subscribe(AST_EVENT_MWI, mwi_event_cb, "MGCP MWI subscription", NULL,
						AST_EVENT_IE_MAILBOX, AST_EVENT_IE_PLTYPE_STR, mbox,
						AST_EVENT_IE_CONTEXT, AST_EVENT_IE_PLTYPE_STR, cntx,
						AST_EVENT_IE_NEWMSGS, AST_EVENT_IE_PLTYPE_EXISTS,
						AST_EVENT_IE_END);
				}
				snprintf(e->rqnt_ident, sizeof(e->rqnt_ident), "%08lx", (unsigned long)ast_random());
				e->msgstate = -1;
				e->amaflags = amaflags;
				ast_format_cap_copy(e->cap, global_capability);
				e->parent = gw;
				e->ncs = ncs;
				e->dtmfmode = dtmfmode;
				if (!ep_reload && e->sub && e->sub->rtp) {
					e->dtmfmode |= MGCP_DTMF_INBAND;
				}
				e->adsi = adsi;
				e->type = TYPE_LINE;
				e->immediate = immediate;
				e->callgroup=cur_callergroup;
				e->pickupgroup=cur_pickupgroup;
				e->callreturn = callreturn;
				e->cancallforward = cancallforward;
				e->singlepath = singlepath;
				e->directmedia = directmedia;
				e->callwaiting = callwaiting;
				e->hascallwaiting = callwaiting;
				e->slowsequence = slowsequence;
				e->transfer = transfer;
				e->threewaycalling = threewaycalling;
				e->onhooktime = time(NULL);
				/* ASSUME we're onhook */
				e->hookstate = MGCP_ONHOOK;
				e->chanvars = copy_vars(chanvars);
				if (!ep_reload) {
					/*snprintf(txident, sizeof(txident), "%08lx", (unsigned long)ast_random());*/
					for (i = 0; i < MAX_SUBS; i++) {
						sub = ast_calloc(1, sizeof(*sub));
						if (sub) {
							ast_verb(3, "Allocating subchannel '%d' on %s@%s\n", i, e->name, gw->name);
							ast_mutex_init(&sub->lock);
							ast_mutex_init(&sub->cx_queue_lock);
							sub->parent = e;
							sub->id = i;
							snprintf(sub->txident, sizeof(sub->txident), "%08lx", (unsigned long)ast_random());
							/*stnrcpy(sub->txident, txident, sizeof(sub->txident) - 1);*/
							sub->cxmode = MGCP_CX_INACTIVE;
							sub->nat = nat;
							sub->gate = NULL;
							sub->sdpsent = 0;
							sub->next = e->sub;
							e->sub = sub;
						} else {
							/* XXX Should find a way to clean up our memory */
							ast_log(LOG_WARNING, "Out of memory allocating subchannel\n");
							return NULL;
						}
					}
					/* Make out subs a circular linked list so we can always sping through the whole bunch */
					/* find the end of the list */
					for (sub = e->sub; sub && sub->next; sub = sub->next);
					/* set the last sub->next to the first sub */
					sub->next = e->sub;

					e->next = gw->endpoints;
					gw->endpoints = e;
				}
			}
		} else if (!strcasecmp(v->name, "trunk") ||
		           !strcasecmp(v->name, "line")) {

			/* locate existing endpoint */
			for (e = gw->endpoints; e; e = e->next) {
				if (!strcasecmp(v->value, e->name)) {
					/* endpoint already exists */
					e->delme = 0;
					ep_reload = 1;
					break;
				}
			}

			if (!e) {
				e = ast_calloc(1, sizeof(*e));
				ep_reload = 0;
			}

			if (e) {
				if (!ep_reload) {
					ast_mutex_init(&e->lock);
					ast_mutex_init(&e->rqnt_queue_lock);
					ast_mutex_init(&e->cmd_queue_lock);
					e->cap = ast_format_cap_alloc_nolock();
					//ast_copy_string(e->name, v->value, sizeof(e->name));//commnet by mkm

					tmpc = strcasestr( v->value,",");
					if(tmpc)
					{
						strncpy(e->telNo ,(tmpc+1),(strlen(tmpc)-1));
						strncpy(e->name ,v->value,(strlen(v->value)-strlen(tmpc)));
					}

					//ast_verb(3,"wwweeeeeeeeee:%s -- %s --  %s \n" ,v->value ,e->name , e->telNo);
					e->needaudit = 1;
				}
				/* XXX Should we really check for uniqueness?? XXX */
				//ast_verb(3,"eeeeeeeeeee:%s \n" ,v->value);
				ast_copy_string(e->accountcode, accountcode, sizeof(e->accountcode));
				ast_copy_string(e->context, context, sizeof(e->context));
				ast_copy_string(e->cid_num, cid_num, sizeof(e->cid_num));
				ast_copy_string(e->cid_name, cid_name, sizeof(e->cid_name));
				ast_copy_string(e->language, language, sizeof(e->language));
				ast_copy_string(e->musicclass, musicclass, sizeof(e->musicclass));
				ast_copy_string(e->mailbox, mailbox, sizeof(e->mailbox));
				ast_copy_string(e->parkinglot, parkinglot, sizeof(e->parkinglot));
				if (!ast_strlen_zero(mailbox)) {
					ast_verb(3, "Setting mailbox '%s' on %s@%s\n", mailbox, gw->name, e->name);
				}
				if (!ep_reload) {
					/* XXX potential issue due to reload */
					e->msgstate = -1;
					e->parent = gw;
				}
				e->amaflags = amaflags;
				ast_format_cap_copy(e->cap, global_capability);
				e->dtmfmode = dtmfmode;
				e->ncs = ncs;
				e->pktcgatealloc = pktcgatealloc;
				e->hangupongateremove = hangupongateremove;
				e->adsi = adsi;
				e->type = (!strcasecmp(v->name, "trunk")) ? TYPE_TRUNK : TYPE_LINE;
				e->immediate = immediate;
				e->callgroup=cur_callergroup;
				e->pickupgroup=cur_pickupgroup;
				e->callreturn = callreturn;
				e->cancallforward = cancallforward;
				e->directmedia = directmedia;
				e->singlepath = singlepath;
				e->callwaiting = callwaiting;
				e->hascallwaiting = callwaiting;
				e->slowsequence = slowsequence;
				e->transfer = transfer;
				e->threewaycalling = threewaycalling;

				/* If we already have a valid chanvars, it's not a new endpoint (it's a reload),
				   so first, free previous mem
				 */
				if (e->chanvars) {
					ast_variables_destroy(e->chanvars);
					e->chanvars = NULL;
				}
				e->chanvars = copy_vars(chanvars);

				if (!ep_reload) {
					e->onhooktime = time(NULL);
					/* ASSUME we're onhook */
					e->hookstate = MGCP_ONHOOK;
					snprintf(e->rqnt_ident, sizeof(e->rqnt_ident), "%08lx", (unsigned long)ast_random());
				}

				for (i = 0, sub = NULL; i < MAX_SUBS; i++) {
					if (!ep_reload) {
						sub = ast_calloc(1, sizeof(*sub));
					} else {
						if (!sub) {
							sub = e->sub;
						} else {
							sub = sub->next;
						}
					}

					if (sub) {
						if (!ep_reload) {
							ast_verb(3, "Allocating subchannel '%d' on %s@%s\n", i, e->name, gw->name);
							ast_mutex_init(&sub->lock);
							ast_mutex_init(&sub->cx_queue_lock);
							ast_copy_string(sub->magic, megaco_subchannel_MAGIC, sizeof(sub->magic));
							sub->parent = e;
							sub->id = i;
							snprintf(sub->txident, sizeof(sub->txident), "%08lx", (unsigned long)ast_random());
							sub->cxmode = MGCP_CX_INACTIVE;
							sub->next = e->sub;
							e->sub = sub;
						}
						sub->nat = nat;
					} else {
						/* XXX Should find a way to clean up our memory */
						ast_log(LOG_WARNING, "Out of memory allocating subchannel\n");
						return NULL;
					}
				}
				if (!ep_reload) {
					/* Make out subs a circular linked list so we can always sping through the whole bunch */
					/* find the end of the list */
					for (sub = e->sub; sub && sub->next; sub = sub->next);
					/* set the last sub->next to the first sub */
					sub->next = e->sub;

					e->next = gw->endpoints;
					gw->endpoints = e;
				}
			}
		} else if (!strcasecmp(v->name, "name") || !strcasecmp(v->name, "lines")||!strcasecmp(v->name, "domain")||!strcasecmp(v->name, "predgt")||!strcasecmp(v->name, "dmap")) {
			/* just eliminate realtime warnings */
		} else {
			ast_log(LOG_WARNING, "Don't know keyword '%s' at line %d\n", v->name, v->lineno);
		}
	}
	if (!ntohl(gw->addr.sin_addr.s_addr) && !gw->dynamic) {
		ast_log(LOG_WARNING, "Gateway '%s' lacks IP address and isn't dynamic\n", gw->name);
		if (!gw_reload) {
			ast_mutex_destroy(&gw->msgs_lock);
			ast_free(gw);
		}

		/* Return NULL */
		gw_reload = 1;
	} else {
		gw->defaddr.sin_family = AF_INET;
		gw->addr.sin_family = AF_INET;
		if (gw->defaddr.sin_addr.s_addr && !ntohs(gw->defaddr.sin_port)) {
			gw->defaddr.sin_port = htons(DEFAULT_MEGACO_C_PORT);
		}
		if (gw->addr.sin_addr.s_addr && !ntohs(gw->addr.sin_port)) {
			gw->addr.sin_port = htons(DEFAULT_MEGACO_C_PORT);
		}
		{
			struct ast_sockaddr tmp1, tmp2;
			struct sockaddr_in tmp3 = {0,};

			tmp3.sin_addr = gw->ourip;
			ast_sockaddr_from_sin(&tmp1, &gw->addr);
			ast_sockaddr_from_sin(&tmp2, &tmp3);
			if (gw->addr.sin_addr.s_addr && ast_ouraddrfor(&tmp1, &tmp2)) {
				memcpy(&gw->ourip, &__ourip, sizeof(gw->ourip));
			} else {
				ast_sockaddr_to_sin(&tmp2, &tmp3);
				gw->ourip = tmp3.sin_addr;
			}
		}
	}

	if (chanvars) {
		ast_variables_destroy(chanvars);
		chanvars = NULL;
	}
	return (gw_reload ? NULL : gw);
}
static enum ast_rtp_glue_result mgcp_get_rtp_peer(struct ast_channel *chan, struct ast_rtp_instance **instance)
{
	struct megaco_subchannel *sub = NULL;

	if (!(sub = ast_channel_tech_pvt(chan)) || !(sub->rtp))
		return AST_RTP_GLUE_RESULT_FORBID;

	*instance = sub->rtp ? ao2_ref(sub->rtp, +1), sub->rtp : NULL;
   // ast_verb(3,"MMMMMMMMMMMMMMMMMMMMMMMMMR   mgcp_get_rtp_peer:%d %s\n",sub->parent->directmedia,ast_channel_name(chan));
	if (sub->parent->directmedia)
		return AST_RTP_GLUE_RESULT_REMOTE;
	else
		return AST_RTP_GLUE_RESULT_LOCAL;
}

static int mgcp_set_rtp_peer(struct ast_channel *chan, struct ast_rtp_instance *rtp, struct ast_rtp_instance *vrtp, struct ast_rtp_instance *trtp, const struct ast_format_cap *cap, int nat_active)
{
	/* XXX Is there such thing as video support with MGCP? XXX */
	struct megaco_subchannel *sub;
	//ast_verb(3,"MMMMMMMMMMMMMMMMMMMMMMMMMMMMSSSSSSSSSSSSSSSSSSSSSSSSSSSSssss mgcp_set_rtp_peer\n");
	sub = ast_channel_tech_pvt(chan);
	if (sub && !sub->alreadygone) {
		transmit_modify_with_sdp(sub, rtp, cap);
		return 0;
	}
	return -1;
}

static void mgcp_get_codec(struct ast_channel *chan, struct ast_format_cap *result)
{
	struct megaco_subchannel *sub = ast_channel_tech_pvt(chan);

	struct megaco_users *p = sub->parent;
	ast_format_cap_copy(result, p->cap);
}

static struct ast_rtp_glue mgcp_rtp_glue = {
	.type = "MEGACO",
	.get_rtp_info = mgcp_get_rtp_peer,
	.update_peer = mgcp_set_rtp_peer,
	.get_codec = mgcp_get_codec,
};


static int acf_channel_read(struct ast_channel *chan, const char *funcname, char *args, char *buf, size_t buflen)
{
	struct megaco_subchannel *sub = ast_channel_tech_pvt(chan);
	int res = 0;

	/* Sanity check */
	if (!chan || ast_channel_tech(chan) != &mgcp_tech) {
		ast_log(LOG_ERROR, "This function requires a valid MGCP channel\n");
		return -1;
	}

	if (!strcasecmp(args, "ncs")) {
		snprintf(buf, buflen, "%s", sub->parent->ncs ?  "yes":"no");
	} else {
		res = -1;
	}
	return res;
}


static void destroy_endpoint(struct megaco_users *e)
{
	struct megaco_subchannel *sub = e->sub->next, *s;
	int i;

	for (i = 0; i < MAX_SUBS; i++) {
		ast_mutex_lock(&sub->lock);
		if (!ast_strlen_zero(sub->cxident)) {
			transmit_connection_del(sub);
		}
		if (sub->rtp) {
			ast_rtp_instance_destroy(sub->rtp);
			sub->rtp = NULL;
		}
		memset(sub->magic, 0, sizeof(sub->magic));
		mgcp_queue_hangup(sub);
		dump_cmd_queues(NULL, sub);
		if(sub->gate) {
			sub->gate->tech_pvt = NULL;
			sub->gate->got_dq_gi = NULL;
			sub->gate->gate_remove = NULL;
			sub->gate->gate_open = NULL;
		}
		ast_mutex_unlock(&sub->lock);
		sub = sub->next;
	}

	if (e->dsp) {
		ast_dsp_free(e->dsp);
	}

	dump_queue(e->parent, e);
	dump_cmd_queues(e, NULL);

	sub = e->sub;
	for (i = 0; (i < MAX_SUBS) && sub; i++) {
		s = sub;
		sub = sub->next;
		ast_mutex_destroy(&s->lock);
		ast_mutex_destroy(&s->cx_queue_lock);
		ast_free(s);
	}

	if (e->mwi_event_sub)
		ast_event_unsubscribe(e->mwi_event_sub);

	if (e->chanvars) {
		ast_variables_destroy(e->chanvars);
		e->chanvars = NULL;
	}

	ast_mutex_destroy(&e->lock);
	ast_mutex_destroy(&e->rqnt_queue_lock);
	ast_mutex_destroy(&e->cmd_queue_lock);
	e->cap = ast_format_cap_destroy(e->cap);
	ast_free(e);
}

static void destroy_gateway(struct megaco_mg *g)
{
	if (g->ha)
		ast_free_ha(g->ha);

	dump_queue(g, NULL);

	ast_free(g);
}

static void prune_gateways(void)
{
	struct megaco_mg *g, *z, *r;
	struct megaco_users *e, *p, *t;

	ast_mutex_lock(&gatelock);

	/* prune megacomg */
	for (z = NULL, g = megacomg; g;) {
		/* prune endpoints */
		for (p = NULL, e = g->endpoints; e; ) {
			if (!g->realtime && (e->delme || g->delme)) {
				t = e;
				e = e->next;
				if (!p)
					g->endpoints = e;
				else
					p->next = e;
				destroy_endpoint(t);
			} else {
				p = e;
				e = e->next;
			}
		}

		if (g->delme) {
			r = g;
			g = g->next;
			if (!z)
				megacomg = g;
			else
				z->next = g;

			destroy_gateway(r);
		} else {
			z = g;
			g = g->next;
		}
	}

	ast_mutex_unlock(&gatelock);
}

static struct ast_variable *add_var(const char *buf, struct ast_variable *list)
{
	struct ast_variable *tmpvar = NULL;
	char *varname = ast_strdupa(buf), *varval = NULL;

	if ((varval = strchr(varname, '='))) {
		*varval++ = '\0';
		if ((tmpvar = ast_variable_new(varname, varval, ""))) {
			tmpvar->next = list;
			list = tmpvar;
		}
	}
	return list;
}

/*! \brief
 * duplicate a list of channel variables, \return the copy.
 */
static struct ast_variable *copy_vars(struct ast_variable *src)
{
	struct ast_variable *res = NULL, *tmp, *v = NULL;

	for (v = src ; v ; v = v->next) {
		if ((tmp = ast_variable_new(v->name, v->value, v->file))) {
			tmp->next = res;
			res = tmp;
		}
	}
	return res;
}


static int reload_config(int reload)
{
	struct ast_config *cfg;
	struct ast_variable *v;
	struct megaco_mg *g;
	struct megaco_subchannel *sub;
	struct megaco_users *e = NULL;
	char *cat;
	struct ast_hostent ahp;
	struct hostent *hp;
	struct ast_format format;
	struct ast_flags config_flags = { reload ? CONFIG_FLAG_FILEUNCHANGED : 0 };
	
	if (gethostname(ourhost, sizeof(ourhost)-1)) {
		ast_log(LOG_WARNING, "Unable to get hostname, MGCP disabled\n");
		return 0;
	}
	ast_verb(3, "-------- Find Megaco hostname '%s' flags:%d \n", ourhost,config_flags.flags);

	cfg = ast_config_load(config, config_flags);

	/* We *must* have a config file otherwise stop immediately */
	if (!cfg) {
		ast_log(LOG_WARNING, "Unable to load config %s, Megaco disabled\n", config);
		return 0;
	} else
	if (cfg == CONFIG_STATUS_FILEUNCHANGED)
	{

		//transmit_MgCheckAlliveMGC
		for (g = megacomg ;g;g = g->next){
				for (e = g->endpoints; e; e = e->next) {
					//ast_verb(3,"Searching on :%s@%s\n",e->name,g->name);
					if(!strcmp(e->name, "ROOT"))
					{
						//ast_verb(3,"--OK ---------------find %s at %s in %s \n",e->name,g->domain,g->name);
						sub = e->sub;
						transmit_MgCheckAlliveMGC(sub);
					}

				}
			}


		return 0;
	}
	else if (cfg == CONFIG_STATUS_FILEINVALID) {
		ast_log(LOG_WARNING, "Config file %s is in an invalid format.  Aborting.\n", config);
		return 0;
	}
	ast_verb(3,"---------------- relaod megaco.conf----------------------- \n");

	memset(&bindaddr, 0, sizeof(bindaddr));
	dtmfmode = 0;

	/* Copy the default jb config over global_jbconf */
	memcpy(&global_jbconf, &default_jbconf, sizeof(struct ast_jb_conf));

	for (v = ast_variable_browse(cfg, "general"); v; v = v->next) {
		ast_verb(3, "2------- relaod megaco.conf \n");
		/* handle jb conf */
		if (!ast_jb_read_conf(&global_jbconf, v->name, v->value)) {
			continue;
		}

		/* Create the interface list */
		if (!strcasecmp(v->name, "bindaddr")) {
			if (!(hp = ast_gethostbyname(v->value, &ahp))) {
				ast_log(LOG_WARNING, "Invalid address: %s\n", v->value);
			} else {
				memcpy(&bindaddr.sin_addr, hp->h_addr, sizeof(bindaddr.sin_addr));
			}
		} else if (!strcasecmp(v->name, "allow")) {
			ast_getformatbyname(v->value, &format);
			if (!format.id) {
				ast_log(LOG_WARNING, "Cannot allow unknown format '%s'\n", v->value);
			} else {
				ast_format_cap_add(global_capability, &format);
			}
		} else if (!strcasecmp(v->name, "disallow")) {
			ast_getformatbyname(v->value, &format);
			if (!format.id) {
				ast_log(LOG_WARNING, "Cannot allow unknown format '%s'\n", v->value);
			} else {
				ast_format_cap_remove(global_capability, &format);
			}
		} else if (!strcasecmp(v->name, "tos")) {
			if (ast_str2tos(v->value, &qos.tos)) {
			    ast_log(LOG_WARNING, "Invalid tos value at line %d, refer to QoS documentation\n", v->lineno	);
			}
		} else if (!strcasecmp(v->name, "tos_audio")) {
			if (ast_str2tos(v->value, &qos.tos_audio))
			    ast_log(LOG_WARNING, "Invalid tos_audio value at line %d, refer to QoS documentation\n", v->lineno);
		} else if (!strcasecmp(v->name, "cos")) {
			if (ast_str2cos(v->value, &qos.cos))
			    ast_log(LOG_WARNING, "Invalid cos value at line %d, refer to QoS documentation\n", v->lineno);
		} else if (!strcasecmp(v->name, "cos_audio")) {
			if (ast_str2cos(v->value, &qos.cos_audio))
			    ast_log(LOG_WARNING, "Invalid cos_audio value at line %d, refer to QoS documentation\n", v->lineno);
		} else if (!strcasecmp(v->name, "port")) {
			if (sscanf(v->value, "%5d", &ourport) == 1) {
				bindaddr.sin_port = htons(ourport);
			} else {
				ast_log(LOG_WARNING, "Invalid port number '%s' at line %d of %s\n", v->value, v->lineno, config);
			}
		} else if (!strcasecmp(v->name, "firstdigittimeout")) {
			firstdigittimeout = atoi(v->value);
		} else if (!strcasecmp(v->name, "gendigittimeout")) {
			gendigittimeout = atoi(v->value);
		} else if (!strcasecmp(v->name, "matchdigittimeout")) {
			matchdigittimeout = atoi(v->value);
		}
	}

	/* mark existing entries for deletion */
	ast_mutex_lock(&gatelock);
	for (g = megacomg; g; g = g->next) {
		g->delme = 1;
		for (e = g->endpoints; e; e = e->next) {
			e->delme = 1;
		}
	}
	ast_mutex_unlock(&gatelock);
//******
	for (cat = ast_category_browse(cfg, NULL); cat; cat = ast_category_browse(cfg, cat)) {
		if (strcasecmp(cat, "general")) {
			ast_mutex_lock(&gatelock);
			if ((g = build_gateway(cat, ast_variable_browse(cfg, cat)))) {
				ast_verb(3, "Added gateway '%s'\n", g->name);
				g->next = megacomg;
				megacomg = g;
			}
			ast_mutex_unlock(&gatelock);

			/* FS: process queue and IO */
			if (monitor_thread == pthread_self()) {
				if (sched) ast_sched_runq(sched);
				if (io) ast_io_wait(io, 10);
			}
		}
	}
//******
	ast_log(LOG_WARNING, "3------- relaod megaco.conf \n");
	/* prune deleted entries etc. */
	prune_gateways();

	if (ntohl(bindaddr.sin_addr.s_addr)) {
		memcpy(&__ourip, &bindaddr.sin_addr, sizeof(__ourip));
	} else {
		hp = ast_gethostbyname(ourhost, &ahp);
		if (!hp) {
			ast_log(LOG_WARNING, "Unable to get our IP address, MGCP disabled\n");
			ast_config_destroy(cfg);
			return 0;
		}
		memcpy(&__ourip, hp->h_addr, sizeof(__ourip));
	}
	if (!ntohs(bindaddr.sin_port))
		bindaddr.sin_port = htons(DEFAULT_MEGACO_C_PORT);
	bindaddr.sin_family = AF_INET;
	ast_mutex_lock(&netlock);
	if (mgcpsock > -1)
		close(mgcpsock);

	if (mgcpsock_read_id != NULL)
		ast_io_remove(io, mgcpsock_read_id);
	mgcpsock_read_id = NULL;

	mgcpsock = socket(AF_INET, SOCK_DGRAM, 0);
	if (mgcpsock < 0) {
		ast_log(LOG_WARNING, "Unable to create MGCP socket: %s\n", strerror(errno));
	} else {
		if (bind(mgcpsock, (struct sockaddr *)&bindaddr, sizeof(bindaddr)) < 0) {
			ast_log(LOG_WARNING, "Failed to bind to %s:%d: %s\n",
				ast_inet_ntoa(bindaddr.sin_addr), ntohs(bindaddr.sin_port),
					strerror(errno));
			close(mgcpsock);
			mgcpsock = -1;
		} else {
			ast_verb(3, "Megaco Listening on %s:%d\n",
					ast_inet_ntoa(bindaddr.sin_addr), ntohs(bindaddr.sin_port));
			ast_set_qos(mgcpsock, qos.tos, qos.cos, "MGCP");
		}
	}
	ast_mutex_unlock(&netlock);
	ast_config_destroy(cfg);
	ast_verb(3, "*********   reload megaco conf finished ************\n");


	return 0;
}

/*! \brief  load_module: PBX load module - initialization ---*/
static int load_module(void)
{
	struct ast_format tmpfmt;

	if (!(global_capability = ast_format_cap_alloc())) {
		return AST_MODULE_LOAD_FAILURE;
	}
	if (!(mgcp_tech.capabilities = ast_format_cap_alloc())) {
		return AST_MODULE_LOAD_FAILURE;
	}
	ast_format_cap_add(global_capability, ast_format_set(&tmpfmt, AST_FORMAT_ULAW, 0));
	ast_format_cap_add(mgcp_tech.capabilities, ast_format_set(&tmpfmt, AST_FORMAT_ULAW, 0));
	ast_format_cap_add(mgcp_tech.capabilities, ast_format_set(&tmpfmt, AST_FORMAT_ALAW, 0));
	if (!(sched = ast_sched_context_create())) {
		ast_log(LOG_WARNING, "Unable to create schedule context\n");
		return AST_MODULE_LOAD_FAILURE;
	}

	if (!(io = io_context_create())) {
		ast_log(LOG_WARNING, "Unable to create I/O context\n");
		ast_sched_context_destroy(sched);
		return AST_MODULE_LOAD_FAILURE;
	}

	if (reload_config(0))
		return AST_MODULE_LOAD_DECLINE;

	/* Make sure we can register our mgcp channel type */
	if (ast_channel_register(&mgcp_tech)) {
		ast_log(LOG_ERROR, "Unable to register channel class 'MGCP'\n");
		io_context_destroy(io);
		ast_sched_context_destroy(sched);
		return AST_MODULE_LOAD_FAILURE;
	}

	ast_rtp_glue_register(&mgcp_rtp_glue);
	ast_cli_register_multiple(cli_megaco, sizeof(cli_megaco) / sizeof(struct ast_cli_entry));

	/* And start the monitor for the first time */
	restart_monitor();

	return AST_MODULE_LOAD_SUCCESS;
}

static char *mgcp_reload(struct ast_cli_entry *e, int cmd, struct ast_cli_args *a)
{
	static int deprecated = 0;

	if (e) {
		switch (cmd) {
		case CLI_INIT:
			e->command = "megaco reload";
			e->usage =
				"Usage: megaco reload\n"
				"       'megaco reload' is deprecated.  Please use 'reload chan_megaco.so' instead.\n";
			return NULL;
		case CLI_GENERATE:
			return NULL;
		}
	}

	if (!deprecated && a && a->argc > 0) {
		ast_log(LOG_WARNING, "'megaco reload' is deprecated.  Please use 'reload chan_megaco.so' instead.\n");
		deprecated = 1;
	}

	ast_mutex_lock(&mgcp_reload_lock);
	if (mgcp_reloading) {
		ast_verbose("Previous megaco reload not yet done\n");
	} else {
		mgcp_reloading = 1;
	}
	ast_mutex_unlock(&mgcp_reload_lock);
	restart_monitor();
	return CLI_SUCCESS;
}

static int reload(void)
{
	mgcp_reload(NULL, 0, NULL);
	return 0;
}

static int unload_module(void)
{
	struct megaco_users *e;
	struct megaco_mg *g;

	/* Check to see if we're reloading */
	if (ast_mutex_trylock(&mgcp_reload_lock)) {
		ast_log(LOG_WARNING, "MEGACO is currently reloading.  Unable to remove module.\n");
		return -1;
	} else {
		mgcp_reloading = 1;
		ast_mutex_unlock(&mgcp_reload_lock);
	}

	/* First, take us out of the channel loop */
	ast_channel_unregister(&mgcp_tech);

	/* Shut down the monitoring thread */
	if (!ast_mutex_lock(&monlock)) {
		if (monitor_thread && (monitor_thread != AST_PTHREADT_STOP)) {
			pthread_cancel(monitor_thread);
			pthread_kill(monitor_thread, SIGURG);
			pthread_join(monitor_thread, NULL);
		}
		monitor_thread = AST_PTHREADT_STOP;
		ast_mutex_unlock(&monlock);
	} else {
		ast_log(LOG_WARNING, "Unable to lock the monitor\n");
		/* We always want to leave this in a consistent state */
		ast_channel_register(&mgcp_tech);
		mgcp_reloading = 0;
		mgcp_reload(NULL, 0, NULL);
		return -1;
	}

	if (!ast_mutex_lock(&gatelock)) {
		for (g = megacomg; g; g = g->next) {
			g->delme = 1;
			for (e = g->endpoints; e; e = e->next) {
				e->delme = 1;
			}
		}

		prune_gateways();
		ast_mutex_unlock(&gatelock);
	} else {
		ast_log(LOG_WARNING, "Unable to lock the megacomg list.\n");
		/* We always want to leave this in a consistent state */
		ast_channel_register(&mgcp_tech);
		/* Allow the monitor to restart */
		monitor_thread = AST_PTHREADT_NULL;
		mgcp_reloading = 0;
		mgcp_reload(NULL, 0, NULL);
		return -1;
	}

	close(mgcpsock);
	ast_rtp_glue_unregister(&mgcp_rtp_glue);
	ast_cli_unregister_multiple(cli_megaco, sizeof(cli_megaco) / sizeof(struct ast_cli_entry));
	ast_sched_context_destroy(sched);

	global_capability = ast_format_cap_destroy(global_capability);
	mgcp_tech.capabilities = ast_format_cap_destroy(mgcp_tech.capabilities);

	return 0;
}

AST_MODULE_INFO(ASTERISK_GPL_KEY, AST_MODFLAG_LOAD_ORDER, "Megaco Protocol (H.248)",
		.load = load_module,
		.unload = unload_module,
		.reload = reload,
		.load_pri = AST_MODPRI_CHANNEL_DRIVER,
		.nonoptreq = "res_pktccops",
	       );

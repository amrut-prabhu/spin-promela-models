mtype = { 
  UPDATED_WEATHER,

  /*14*/ IDLE, /* CM and for connected clients*/
  /*13*/ PRE_INITIALIZING,
  /*12*/ INITIALIZING,
  /*11*/ POST_INITIALIZING,

  /*10*/ DISCONNECTED, 

  /* WCP */ 
  /*9*/ ENABLED, 
  /*8*/ DISABLED, 

  /*7*/ CONNECT_REQ, 
  /*6*/ GET_NEW_WEATHER_REQ, 
  /*5*/ GET_NEW_WEATHER_RESP, 
  /*4*/ USE_NEW_WEATHER_REQ, 
  /*3*/ USE_NEW_WEATHER_RESP,

  /*2*/ ACK, 
  /*1*/ NACK,
}

#define DUMMY_VAL 100

/* Each client uses one data channel and one ack channel for communication with WCP*/
chan cm_chan = [1] of { mtype, byte, byte };
chan client_chan[3] = [1] of { mtype };

/* Initialize components */
mtype cm_status = IDLE;
mtype wcp_status = ENABLED;
mtype client_status[3] = DISCONNECTED;

inline set_is_successful() {
  is_successful = DUMMY_VAL;
  do
  :: is_successful == DUMMY_VAL ->
      if
      :: is_successful = 1
      :: is_successful = 0
      fi
  :: else ->
      break;
  od
}

proctype Client(byte id)
{
  // TODO: Should have its own status?
  byte is_successful;
  mtype req;
  mtype resp;

  // L1: do 
  do 
    /* Step A1. Connection request */
    :: (client_status[id] == DISCONNECTED) -> 
        cm_chan ! CONNECT_REQ, id, DUMMY_VAL;

        client_chan[id] ? resp;
        if
        :: (resp == NACK) -> client_status[id] = DISCONNECTED;
        :: (resp == ACK) -> skip;
        fi

    :: (client_status[id] == IDLE) -> 
        printf("!!!==Client %d: IDLE\n", id);

    :: client_chan[id] ? req ->
        if
        :: (client_status[id] == INITIALIZING) -> {
            // printf("%d: INIT Waiting\n", id);
            // client_chan[id] ? req; 
            printf("%d: INIT Get Received\n", id);

            /* Step A4a. Client response to Get New Weather info */
            if :: (req == GET_NEW_WEATHER_REQ) -> {
                set_is_successful();
                cm_chan ! GET_NEW_WEATHER_RESP, id, is_successful;
            printf("%d: INIT Sent\n", id);
            }
            
            :: else ->
                printf("Error: not GET \n");
                skip;
            fi;
        }

        :: (client_status[id] == POST_INITIALIZING) ->
            // printf("%d: INIT Waiting \n", id);
            // client_chan[id] ? req; 
            printf("%d: POST Use Received %d\n", id, req);

            // do
            // :: client_chan[id] ? req
            // :: timeout -> break
            // od
            /* needs timeout for the case when CM disconnects client (if is_successful is 0) */

            /* Step A5a. Client response to Get New Weather info */
            if :: (req == USE_NEW_WEATHER_REQ) -> {
                set_is_successful();
                cm_chan ! USE_NEW_WEATHER_RESP, id, is_successful;
            }
            
            /* Step A4b. Disconnected */
            :: (req == NACK) -> skip; //goto L1 // FIXME:
            
            :: else ->
                printf("Error: not USE \n");
                skip;
            fi;
            printf("%d: POST Use done\n", id);
        
        fi

    :: else ->
        ;
		// break
  od
}

proctype CM()
{
  byte client_id = DUMMY_VAL; // current client being connected
  byte num_connected_clients;
  byte connected_clients[3] = DUMMY_VAL;

  mtype req;
  byte id, val;

  do
  :: cm_chan ? req, id, val -> 
      if 
      /* Step A2. Connection response */
      :: (req == CONNECT_REQ) ->
          if :: (cm_status == IDLE) -> 
              cm_status = PRE_INITIALIZING;
              client_status[id] = PRE_INITIALIZING;
              wcp_status = DISABLED;
              client_id = id;

              client_chan[id] ! ACK;
          :: else -> 
              client_chan[id] ! NACK; // refuse the connection
          fi

      /* Step A4b. CM action to client response for Get New Weather info */
      :: (cm_status == INITIALIZING && id == client_id && req == GET_NEW_WEATHER_RESP) ->
          printf("CM: rec get = %d from %d\n", val, id);
          if :: (val == 1) ->
              atomic { // FIXME:
                  client_chan[client_id] ! USE_NEW_WEATHER_REQ;
                  cm_status = POST_INITIALIZING;
                  client_status[client_id] = POST_INITIALIZING;
              }

          :: else ->
            //   client_chan[client_id] ! NACK; // FIXME:
              client_status[client_id] = DISCONNECTED;
              cm_status = IDLE;
              client_id = DUMMY_VAL;
              // FIXME: Enable WCP?
          fi

      /* Step A5b. CM action to client response for Get New Weather info */
      :: (cm_status == POST_INITIALIZING && id == client_id && req == USE_NEW_WEATHER_RESP) ->
          printf("CM: POST rec Use");
          if :: (val == 1) ->
              cm_status = IDLE;
              client_status[client_id] = IDLE;
              wcp_status = ENABLED;
              client_id = DUMMY_VAL;

          :: else ->
              client_status[client_id] = DISCONNECTED;
              wcp_status = ENABLED;
              cm_status = IDLE;
              client_id = DUMMY_VAL;
          fi

      fi

  /* Step A3. Pre-init Get New Weather info */
  :: (cm_status == PRE_INITIALIZING) ->
      atomic { // FIXME:
          client_chan[client_id] ! GET_NEW_WEATHER_REQ;
          printf("CM: PRE sent\n");
          cm_status = INITIALIZING;
          client_status[client_id] = INITIALIZING;
      }

  // TODO: Timeouts for all receives?
  /* 
  :: timeout -> break 
  A more traditional use is to place a timeout as an alternative to a potentially blocking statement, 
  to guard against a system deadlock if the statement becomes permanently blocked.
  */
  od
}

proctype WCP()
{
  do
  :: (wcp_status == ENABLED) ->
    if :: (cm_chan ?? [UPDATED_WEATHER, DUMMY_VAL, DUMMY_VAL] == false) ->
        cm_chan ! UPDATED_WEATHER, DUMMY_VAL, DUMMY_VAL;
    :: else
    fi
  od
}

init {
  atomic {
    run CM();
    // run WCP();

    run Client(0); 
    run Client(1); 
    run Client(2)
  }
}

// active proctype monitor()
// {
//     do
//         :: true -> assert(client_status[0] != IDLE && client_status[1] != IDLE && client_status[2] != IDLE);
//     od;
// }

#define p0 client_status[0] == IDLE
#define p1 client_status[1] == IDLE
#define p2 client_status[2] == IDLE

ltl v1 { []<>(p0 && p1 && p2) }


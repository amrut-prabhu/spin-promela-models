mtype = { 
  IDLE, /* CM */ 
  PRE_INITIALIZING, INITIALIZING, POST_INITIALIZING, /* CM, Client */ 
  CONNECTED, DISCONNECTED, /* Client */
  ENABLED, DISABLED, /* WCP */

  CONNECT_REQ, GET_NEW_WEATHER_REQ, GET_NEW_WEATHER_RESP, USE_NEW_WEATHER_REQ, USE_NEW_WEATHER_RESP,
  ACK, NACK,
}

/* Each client uses one data channel and one ack channel for communication with WCP*/
chan cm_chan = [1] of { mtype, byte, byte };
chan client_chan[3] = [1] of { mtype };

/* Initialize components */
mtype cm_status = IDLE;
mtype wcp_status = ENABLED;
mtype client_status[3] = DISCONNECTED;

proctype Client(byte id)
{
  // TODO: Should have its own status?
  mtype req, resp;

  do 
    :: (client_status[id] == DISCONNECTED) -> 
        cm_chan ! CONNECT_REQ, id; /* Connection request */

        client_chan[id] ? resp;
        (resp == NACK) -> client_status[id] = DISCONNECTED

    :: (client_status[id] == PRE_INITIALIZING 
          || client_status[id] == INITIALIZING 
          || client_status[id] == POST_INITIALIZING) ->

        client_chan[id] ? req;

        byte isSuccessful = -1;
        do
        :: isSuccessful == -1 ->
            if
            :: isSuccessful = 1
            :: isSuccessful = 0
            fi
        :: else ->
            break
        od

        if
        :: (req == GET_NEW_WEATHER_REQ) -> 
            cm_chan ! GET_NEW_WEATHER_RESP, id, isSuccessful;

        :: (req == USE_NEW_WEATHER_REQ) -> 
            cm_chan ! USE_NEW_WEATHER_RESP, id, isSuccessful;

        fi
        // TODO: Timeouts for all receives?
  od
}

proctype CM()
{
  byte client_id = -1;
  
  mtype req;
  byte id, val;

  do
  :: cm_chan ? req, id, val -> 
      if 
      :: (req == CONNECT_REQ) ->
          if :: (cm_status == IDLE) -> 
              cm_status = PRE_INITIALIZING;
              client_status[id] = PRE_INITIALIZING;
              wcp_status = DISABLED;
              client_id = id;

              client_chan[id] ! ACK;
          :: else -> 
              client_chan[id] ! NACK;
          fi

      :: (req == INITIALIZING && id == client_id) ->
          if :: (val == 1) ->
              client_chan[client_id] ! USE_NEW_WEATHER_REQ;
              cm_status = POST_INITIALIZING;
              client_status[client_id] = POST_INITIALIZING;

          :: else ->
              client_status[client_id] = DISCONNECTED;
              cm_status = IDLE;
          fi

      :: (req == POST_INITIALIZING && id == client_id) ->
          if :: (val == 1) ->
              cm_status = IDLE;
              client_status[client_id] = IDLE;
              wcp_status = ENABLED;

          :: else ->
              client_status[client_id] = DISCONNECTED;
              wcp_status = ENABLED;
              cm_status = IDLE;
          fi

      fi

  :: (cm_status == PRE_INITIALIZING) ->
      client_chan[client_id] ! GET_NEW_WEATHER_REQ;
      cm_status = INITIALIZING;
      client_status[client_id] = INITIALIZING;

  // :: timeout -> ackchan!in
  /* :: timeout -> break 
  A more traditional use is to place a timeout as an alternative to a potentially blocking statement, to guard against a system deadlock if the statement becomes permanently blocked.
  */
  od
}

init {
  run CM(); 
  run Client(0); 
  run Client(1); 
  run Client(2)
}

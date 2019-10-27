mtype = { 
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

  L1: do 
    /* Step 1. Connection request */
    :: (client_status[id] == DISCONNECTED) -> 
        cm_chan ! CONNECT_REQ, id, 0; // Dummy val 

        mtype resp;
        client_chan[id] ? resp;
        if
        :: (resp == NACK) -> client_status[id] = DISCONNECTED;
        :: (resp == ACK) -> client_status[id] = PRE_INITIALIZING;
        fi

    :: (client_status[id] == PRE_INITIALIZING  || client_status[id] == INITIALIZING) ->
        mtype req;
        // do
        // :: client_chan[id] ? req
        // :: timeout -> break
        // od
        /* needs timeout for the case when CM disconnects client (if isSuccessful is 0) */
        client_chan[id] ? req; 

        byte isSuccessful = 100;
        do
        :: isSuccessful == 100 ->
            if
            :: isSuccessful = 1
            :: isSuccessful = 0
            fi
        :: else ->
            break
        od

        if
        /* Step 4a. Client response to Get New Weather info */
        :: (req == GET_NEW_WEATHER_REQ) -> 
            cm_chan ! GET_NEW_WEATHER_RESP, id, isSuccessful;

        /* Step 5. Client response to Get New Weather info */
        :: (req == USE_NEW_WEATHER_REQ) -> 
            cm_chan ! USE_NEW_WEATHER_RESP, id, isSuccessful;
        
        :: (req == NACK) -> goto L1
        fi

    :: else ->
        ;
		// break
  od
}

proctype CM()
{
  byte client_id = 100;
  
  mtype req;
  byte id, val;

  do
  :: cm_chan ? req, id, val -> 
      if 
      /* Step 2. Connection response */
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

      /* Step 4b. CM action to client response for Get New Weather info */
      :: (cm_status == INITIALIZING && id == client_id && req == GET_NEW_WEATHER_RESP) ->
          if :: (val == 1) ->
              client_chan[client_id] ! USE_NEW_WEATHER_REQ;
              cm_status = POST_INITIALIZING;
              client_status[client_id] = POST_INITIALIZING;

          :: else ->
              client_chan[client_id] ! NACK; //
              client_status[client_id] = DISCONNECTED;
              cm_status = IDLE;
          fi

      /* Step 5b. CM action to client response for Get New Weather info */
      :: (cm_status == POST_INITIALIZING && id == client_id && req == USE_NEW_WEATHER_RESP) ->
          if :: (val == 1) ->
              cm_status = IDLE;
              client_status[client_id] = IDLE;
              wcp_status = ENABLED;
              client_id = 100;

          :: else ->
              client_status[client_id] = DISCONNECTED;
              wcp_status = ENABLED;
              cm_status = IDLE;
              client_id = 100;
          fi

      fi

  /* Step 3. Pre-init Get New Weather info */
  :: (cm_status == PRE_INITIALIZING) ->
      client_chan[client_id] ! GET_NEW_WEATHER_REQ;
      cm_status = INITIALIZING;
      client_status[client_id] = INITIALIZING;

  // TODO: Timeouts for all receives?
  /* 
  :: timeout -> break 
  A more traditional use is to place a timeout as an alternative to a potentially blocking statement, 
  to guard against a system deadlock if the statement becomes permanently blocked.
  */
  od
}

init {
  run CM(); 
  run Client(0); 
  run Client(1); 
  run Client(2)
}

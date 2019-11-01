mtype = { 
  /*21*/ POST_REVERTING, 
  /*20*/ POST_UPDATING,
  /*19*/ UPDATING,
  /*18*/ PRE_UPDATING,

  /*17*/ IDLE, /* CM and for connected clients*/
  /*16*/ PRE_INITIALIZING,
  /*15*/ INITIALIZING,
  /*14*/ POST_INITIALIZING,

  /*13*/ DISCONNECTED, 

  /* WCP */ 
  /*12*/ ENABLED, 
  /*11*/ DISABLED, 

  /*10*/ USER_UPDATED_WEATHER, /* WCP message */ 

  /*9*/ CONNECT_REQ, 
  /*8*/ GET_NEW_WEATHER_REQ, 
  /*7*/ GET_NEW_WEATHER_RESP, 
  /*6*/ USE_NEW_WEATHER_REQ, 
  /*5*/ USE_NEW_WEATHER_RESP,
  /*4*/ USE_OLD_WEATHER_REQ, 
  /*3*/ USE_OLD_WEATHER_RESP,

  /*2*/ ACK, 
  /*1*/ NACK,
}

#define DUMMY_VAL 100

chan client_chan[3] = [1] of { mtype };
chan cm_chan = [1] of { mtype, byte, byte };

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

    :: client_chan[id] ? req ->
      if
      /* Step A4a. B4a. Client response to Get New Weather info */
      :: (client_status[id] == INITIALIZING  || client_status[id] == UPDATING) -> {
        if :: (req == GET_NEW_WEATHER_REQ) -> {
          set_is_successful();
          cm_chan ! GET_NEW_WEATHER_RESP, id, is_successful;
        }
          
        :: else ->
          printf("Error: not GET \n");
          skip;
        fi;
      }

      /* Step A5a. B5a. Client response to Use New Weather info */
      :: (client_status[id] == POST_INITIALIZING || client_status[id] == POST_UPDATING) ->
        // do
        // :: client_chan[id] ? req
        // :: timeout -> break
        // od
        /* needs timeout for the case when CM disconnects client (if is_successful is 0) */

        if :: (req == USE_NEW_WEATHER_REQ) -> {
            set_is_successful();
            cm_chan ! USE_NEW_WEATHER_RESP, id, is_successful;
        }
        /* Step A4b. Disconnected */
        :: (req == NACK) -> skip; //goto L1 // FIXME: not needed?
        :: else ->
            printf("Error: not USE \n");
            skip;
        fi;

      /* Step B6a. Client response to Use Old Weather info */
      :: (client_status[id] == POST_REVERTING) -> 
        if :: (req == USE_OLD_WEATHER_REQ) -> {
          set_is_successful();
          cm_chan ! USE_OLD_WEATHER_RESP, id, is_successful;
        }
        :: else ->
          printf("Error: not USE \n");
          skip;
        fi;
        
      fi /* end branching on request type */
  od
}

inline message_connected_clients(msg) {
  for (i : 0..2) { // TODO: num_connected_clients - 1
    id = connected_clients[i];
    if :: (id < 3) ->
      client_chan[id] ! msg;
    :: else
    fi
  }   
}

inline set_connected_clients_status(status) {
  for (i : 0..2) { // TODO: num_connected_clients - 1
    id = connected_clients[i];

    if :: (id < 3) ->
      client_status[id] = status;
    :: else
    fi
  }   
}

inline check_are_all_successful() {
  are_all_successful = true;   

  for (i : 0..2) { /* TODO: */
    id = connected_clients[i];

    if :: (id < 3 && connected_clients_responses[i] == 0) ->
      are_all_successful = false;
    :: else
    fi

    connected_clients_responses[i] = DUMMY_VAL;
  }

  num_connected_clients_responses = 0;
}

inline disconnect_connected_clients() {
  for (i : 0..2) {
    id = connected_clients[i];

    if :: (id < 3) -> 
      client_status[id] = DISCONNECTED;
    :: else
    fi

    connected_clients[i] = DUMMY_VAL;
  }

  num_connected_clients = 0;
}

proctype CM()
{
  byte client_id = DUMMY_VAL; // current client being connected
  byte num_connected_clients = 0;
  byte connected_clients[3] = DUMMY_VAL;

  byte num_connected_clients_responses = 0;
  byte connected_clients_responses[3] = DUMMY_VAL;

  mtype req;
  byte id, val, i;
  bool are_all_successful;
  
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
      if :: (val == 1) ->
        cm_status = IDLE;
        client_status[client_id] = IDLE;
        wcp_status = ENABLED;

        connected_clients[num_connected_clients] = client_id;
        num_connected_clients = num_connected_clients + 1;

        client_id = DUMMY_VAL;

      :: else ->
        client_status[client_id] = DISCONNECTED;
        wcp_status = ENABLED;
        cm_status = IDLE;
        client_id = DUMMY_VAL;
      fi


    /* Step B2. CM action to client response for Get New Weather info */
    :: (req == USER_UPDATED_WEATHER) ->
      // Prevent any further update requests by WCP before completion of current update
      if :: (cm_status == IDLE) ->
        atomic {
          cm_status = PRE_UPDATING;
          set_connected_clients_status(PRE_UPDATING);
          wcp_status = DISABLED; 
        }

        // FIXME:? move the next 3 blocks for response collection into PRE_UPDATING?
        if :: (num_connected_clients == 0) ->
          cm_status = IDLE;
          wcp_status = ENABLED; // FIXME:
        :: else
        fi

      :: else
      fi

    :: (cm_status == UPDATING && req == GET_NEW_WEATHER_RESP) ->
      connected_clients_responses[num_connected_clients_responses] = val;
      num_connected_clients_responses = num_connected_clients_responses + 1;

      /* Step B4. Process Get New Weather info results */  
      if :: (num_connected_clients_responses == num_connected_clients) ->
        check_are_all_successful();

        if :: are_all_successful ->
          atomic {
            message_connected_clients(USE_NEW_WEATHER_REQ);
            cm_status = POST_UPDATING;
            set_connected_clients_status(POST_UPDATING);
          }
        :: else ->
          atomic {
            message_connected_clients(USE_OLD_WEATHER_REQ);
            cm_status = POST_REVERTING;
            set_connected_clients_status(POST_REVERTING);
          }
        fi

      :: else
      fi

    :: (cm_status == POST_UPDATING && req == USE_NEW_WEATHER_RESP) ->
      connected_clients_responses[num_connected_clients_responses] = val;
      num_connected_clients_responses = num_connected_clients_responses + 1;

      /* Step B5. Process Use New Weather info results */  
      if :: (num_connected_clients_responses == num_connected_clients) ->
        check_are_all_successful();

        if :: are_all_successful ->
          cm_status = IDLE;
          set_connected_clients_status(IDLE);
          wcp_status = ENABLED;
        :: else ->
          disconnect_connected_clients();
          wcp_status = ENABLED;
          cm_status = IDLE;
        fi

      :: else
      fi

    :: (cm_status == POST_REVERTING && req == USE_OLD_WEATHER_RESP) ->
      connected_clients_responses[num_connected_clients_responses] = val;
      num_connected_clients_responses = num_connected_clients_responses + 1;

      /* Step B6. Process Old New Weather info results */  
      if :: (num_connected_clients_responses == num_connected_clients) ->
        check_are_all_successful();

        if :: are_all_successful ->
          cm_status = IDLE;
          set_connected_clients_status(IDLE);
          wcp_status = ENABLED;
        :: else ->
          disconnect_connected_clients();
          wcp_status = ENABLED;
          cm_status = IDLE;
        fi

      :: else
      fi

    fi; /* end branching on request type */



  /* Step A3. Pre-init Get New Weather info */
  :: (cm_status == PRE_INITIALIZING) ->
    atomic { // FIXME:
      client_chan[client_id] ! GET_NEW_WEATHER_REQ;
      cm_status = INITIALIZING;
      client_status[client_id] = INITIALIZING;
    }

  /* Step B3. Pre-upd Get New Weather info */
  :: (cm_status == PRE_UPDATING) ->
    atomic { // TODO: needed?
      message_connected_clients(GET_NEW_WEATHER_REQ);
      cm_status = UPDATING;
      set_connected_clients_status(UPDATING);
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
    /* Step B1. Send update message to CM */
    if :: (cm_chan ? [USER_UPDATED_WEATHER, DUMMY_VAL, DUMMY_VAL] == false) ->
      // Remove unread message from buffer and send a new one
      // TODO: violates q2?
      if :: (wcp_status == ENABLED) ->
        cm_chan ! USER_UPDATED_WEATHER, DUMMY_VAL, DUMMY_VAL;
      :: else
      fi

    :: else
    fi
  od
}

init {
  atomic {
    run WCP();
    run CM();

    run Client(0); 
    run Client(1); 
    run Client(2)
  }
}


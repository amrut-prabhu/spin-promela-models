mtype = { 
  STATIONARY,
  TRAVELLING,
  
  REFUSE,
  OFFER,

  NEW_ORDER,
  ASSIGN_ORDER,
}

// #define LEFT -1
// #define RIGHT 1
// #define NONE 0

// #define NUM_STATIONS 6;
// #define NUM_SHUTTLES 3;
// #define NUM_ORDERS 2 

#define DUMMY_VAL 100

typedef Travel {
	byte start; /* start station (1-6) */
  int dir /* direction (1, 0, -1) */
};

Travel shuttle_travel[ 3 ];

typedef Order {
  byte start;
  byte dest;
  byte size;
}

chan system_chan = [1] of { mtype, byte, Order, int };
chan shuttle_chan[ 3 ] = [1] of { mtype, Order };

inline abs_diff(a, b) {
  if :: (a > b) ->
    diff = a - b;
  :: else ->
    diff = b - a;
  fi;
}

inline remainder(x, y, z) {
  if :: (x < 0) ->
    z = ((x + y) % y);
  :: else ->
    z = x % y;
  fi;
}

// inline min(x, y, z) {
//   if :: (x < y) ->
//     z = x;
//   :: else ->
//     z = y;
//   fi
// }

inline set_direction(s1, d1) {
  remainder((s1 - d1), 6 , i);
  remainder((d1 - s1), 6 , j);

  if 
  :: (i < j) ->
    shuttle_travel[id].dir = -1 ;
  :: (j < i) ->
    shuttle_travel[id].dir = 1 ;
  fi;
}

inline get_distance(abc, xyz) {
  remainder(abc - xyz, 6 , i);
  remainder(xyz - abc, 6 , j);

  if :: (i < j) ->
    distance = i;
  :: else ->
    distance = j;
  fi;
}

proctype Shuttle(byte idx; byte start_station; int capacity; int charge) {
  byte id = idx - 1;
  byte curr_station = start_station;
  int load;
  mtype status = STATIONARY;
  Order orders[ 2 ]; // Number of orders assigned to system is not limited; No need for modulo
  byte num_orders = 0;
  byte curr_order = 0;

  byte distance, i, j;
  bool are_passengers_loaded = false; 
  bool can_travel = true;
  mtype msg;
  Order o;
  int payment;

  shuttle_travel[id].start = start_station;
  shuttle_travel[id].dir = 0 ;

  do
  :: shuttle_chan[id] ? msg, o ->
    if 
    /* Process and send offer for new order */
    :: (msg == NEW_ORDER) ->
      get_distance(o.start, curr_station);

      if :: (load + o.size <= capacity && distance <= 2) ->
        payment = charge * o.size;
        system_chan ! OFFER, id, o, payment;

      :: else ->
        system_chan ! REFUSE, id, o, 0;
      fi;

    /* Process assigned order */
    :: (msg == ASSIGN_ORDER) ->
      // printf("num=%d\n", num_orders);

      orders[num_orders].start = o.start;
      orders[num_orders].dest = o.dest;
      orders[num_orders].size = o.size;
      num_orders = num_orders + 1;
    fi;

  /* Complete the assigned orders, one at a time */
  :: (curr_order != num_orders) ->
    if 
    /* Load passengers (if possible) from start station */
    :: curr_station == orders[curr_order].start && !are_passengers_loaded ->
      (load + orders[curr_order].size <= capacity) -> {
        load = load + orders[curr_order].size;
        are_passengers_loaded = true;
      
        /* Set direction to travel to dest */      
        set_direction(curr_station, orders[curr_order].dest); 
      }
      // printf("3Shuttle %d: loaded dir=%d\n", id, shuttle_travel[id].dir);

    /* Unload passengers (if possible) at dest station */
    :: curr_station == orders[curr_order].dest && are_passengers_loaded ->
      load = load - orders[curr_order].size;

      status = STATIONARY;
      shuttle_travel[id].start = curr_station;
      shuttle_travel[id].dir = 0 ;

      // printf("4Shuttle %d: finished order %d\n", id, curr_order);

      curr_order = curr_order + 1;
      are_passengers_loaded = false;
    
    :: else ->
      /* Set direction to travel to start */      
      if :: (shuttle_travel[id].dir == 0 ) -> 
        set_direction(curr_station, orders[curr_order].start); 
        // printf("1Shuttle %d: start dir= %d\n", id, shuttle_travel[id].dir);

      :: else
      fi
      
      // printf("2Shuttle %d: travelling\n", id);
      
      /* Travel to order start/dest */
      atomic {
        can_travel = true;
        for (i : 0 .. 3 - 1) {
          if :: (shuttle_travel[i].start == curr_station 
            && shuttle_travel[i].dir == shuttle_travel[id].dir
            && i != id) ->
            can_travel = false;
          :: else
          fi
        }

        if :: can_travel -> 
          shuttle_travel[id].start = curr_station;

          // travel and update curr_station to the arriving station
          remainder(shuttle_travel[id].start + shuttle_travel[id].dir, 6 , curr_station);
          status = TRAVELLING;
          :: else
        fi;
      }
    fi;

  od
}

inline send_to_all(msg, o) {
  for (i : 0 .. 3 - 1) {
    shuttle_chan[i] ! msg, o;
  }
}

proctype System() {
  Order o;
  mtype msg;

  byte i, id, min_id[2], num_responded[2];
  bool has_assigned[2];
  int min_payment[2], payment, idx;
  int num_orders = 0;
  Order orders[2];
  
  do
  :: system_chan ? msg, id, o, payment ->
    if 
    /* Inform shuttles of new order */
    :: (msg == NEW_ORDER) ->
      orders[num_orders].start = o.start;
      orders[num_orders].dest = o.dest;
      orders[num_orders].size = o.size;
      
      min_payment[num_orders] = 1000000;
      num_responded[num_orders] = 0;

      num_orders = num_orders + 1;

      send_to_all(NEW_ORDER, o);
      
    /* Process offers for new order */
    :: else -> {
      // Get order index
      for (i : 0 .. num_orders - 1) {
        if :: (orders[i].start == o.start 
          && orders[i].dest == o.dest 
          && orders[i].size == o.size) ->
          idx = i;
        :: else
        fi
      }

      num_responded[idx] = num_responded[idx] + 1;

      if
      :: (msg == OFFER) ->
        if :: (min_payment[idx] == 1000000) ->
          min_id[idx] = id;
          min_payment[idx] = payment;
        :: else ->
          if :: (payment < min_payment[idx]) -> // If equal, don't assign to the later offer
            min_id[idx] = id;
            min_payment[idx] = payment;
          :: else
          fi
        fi

      :: (msg == REFUSE) ->
        skip;
      fi
    }
      
    fi

  /* Assign order to an offer */
  :: (!has_assigned[0] || !has_assigned[1]) ->
    for (i : 0 .. num_orders - 1) {
      if :: (num_responded[i] == 3 && !has_assigned[i]) ->
        shuttle_chan[min_id[i]] ! ASSIGN_ORDER, orders[i];
        has_assigned[i] = true;
      :: else 
      fi
    }
  od

}

init {
  atomic {
    run System();
    
    run Shuttle(1, 1, 5, 2);
    run Shuttle(2, 1, 8, 4);
    run Shuttle(3, 2, 10, 3);
  }

  Order o1;
  o1.start = 1;
  o1.dest = 3;
  o1.size = 4;
  system_chan ! NEW_ORDER, DUMMY_VAL , o1, DUMMY_VAL;

  Order o2;
  o2.start = 2;
  o2.dest = 3;
  o2.size = 1;
  system_chan ! NEW_ORDER, DUMMY_VAL , o2, DUMMY_VAL;
}

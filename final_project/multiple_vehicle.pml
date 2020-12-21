#define TOTAL_VEHICLES 4
#define TOTAL_LANES 4
#define MAX_SPEED 10
#define MIN_SPEED 2
#define MAX_ROAD_LENGTH 100
#define MIN_SAFETY_DISTANCE 15
#define TOTAL_SIM_FRAMES 200

/* Struct definitions */
typedef Vehicle {
  bit finish;
  short id;
  byte lane;
  short position;
  short speed;
};

/* Global variables */
short gActionNow = -1;
short gFrameCounter = 0;
short gFinishedCars = 0;
Vehicle gCars[TOTAL_VEHICLES];

/* Communication channels */
chan abs_msg = [0] of {int};
chan collision_msg = [0] of {short};
chan print_msg = [0] of {short};

proctype VehicleBot(byte id) {
  /* A bot that runs vehicle */
  /* running actions */
  do
    ::gActionNow == gCars[id].id ->
      gActionNow = -1;
      byte possible_action = 15;
      do
        ::(possible_action & 1 > 0) ->
          atomic {
            /* full speed */
            int collision = 0;
            int current_speed = gCars[id].speed;
            gCars[id].speed = MAX_SPEED;
            collision_msg!1;
            collision_msg?collision;
            if
              :: collision == 0 -> break;
              :: else ->
                gCars[id].speed = current_speed;
                possible_action = possible_action & 14;
                skip;
            fi
          }
        :: (possible_action & 2 > 0) ->
          atomic {
            /* stop */
            int collision = 0;
            int current_speed = gCars[id].speed;
            gCars[id].speed = MIN_SPEED;
            collision_msg!1;
            collision_msg?collision;
            if
              :: collision == 0 -> break;
              :: else ->
                gCars[id].speed = current_speed;
                possible_action = possible_action & 13;
                skip;
            fi
          }
        :: (possible_action & 4 > 0) ->
          atomic {
            /* change to left */
            int collision = 0;
            short current_lane = gCars[id].lane;
            if
              :: gCars[id].lane > 0 ->gCars[id].lane--;
              :: else -> skip;
            fi
            collision_msg!1;
            collision_msg?collision;
            if
              :: collision == 0 -> break;
              :: else ->
                gCars[id].lane = current_lane;
                possible_action = possible_action & 11;
                skip;
            fi
          }
        :: (possible_action & 8 > 0) ->
          atomic {
            /* change to right */
            int collision = 0;
            short current_lane = gCars[id].lane;
            if
              :: gCars[id].lane < TOTAL_LANES - 1 ->gCars[id].lane++;
              :: else -> skip;
            fi
            collision_msg!1;
            collision_msg?collision;
            if
              :: collision == 0 -> break;
              :: else ->
                gCars[id].lane = current_lane;
                possible_action = possible_action & 7;
                skip;
            fi
          }
        :: possible_action == 0 ->
            break;
      od
    ::gCars[id].finish == 1 -> break;
  od
}

/*
  In every iteration one vehicle
  can only do one thing.
*/
proctype AbsService(chan AbsMsg) {
  /* a, abs(a) */
  int a;
  do
    :: gFinishedCars >= TOTAL_VEHICLES -> break;
    :: gFinishedCars < TOTAL_VEHICLES ->
        AbsMsg?a;
        if
          :: a >= 0 -> AbsMsg!a;
          :: else -> AbsMsg!(-a);
        fi
  od
}

proctype PrintStateService(chan PrintMsg) {
  short id;
  PrintMsg?id;
  printf("Car %d has hard time at: \n", id);
  int car;
  for (car : 0 .. TOTAL_VEHICLES - 1) {
    printf("car[%d], (%d, %d, %d)\n", car,
        gCars[car].lane, gCars[car].position, gCars[id].speed);
  }
  printf("\n");
}

proctype CheckCollisionService(chan CollisionMsg) {
  /* second */
  int second = 0;
  do
    ::gFinishedCars >= TOTAL_VEHICLES -> break;
    ::gFinishedCars < TOTAL_VEHICLES ->
      CollisionMsg?second;
      int i = 0;
      int j = 0;
      for (i : 0 .. TOTAL_VEHICLES - 1) {
        for (j : 0 .. TOTAL_VEHICLES - 1) {
          if
            :: (gCars[i].finish == 0) && (gCars[i].finish == 0) -> 
              if 
                :: (i != j) && (gCars[i].lane == gCars[j].lane) ->
                  atomic {
                    int a = gCars[i].position + gCars[i].speed * second
                        - gCars[j].position - gCars[j].speed * second;
                    abs_msg!a;
                    abs_msg?a;
                    if
                      ::a < MIN_SAFETY_DISTANCE ->
                        CollisionMsg!1;
                      :: else -> skip;
                    fi
                  }
                ::else -> skip;
              fi
            :: else -> skip;
          fi
        }
      }
      CollisionMsg!0;
  od
}

proctype GlobalLockStep() {
  do
    ::gFinishedCars >= TOTAL_VEHICLES -> break;
    ::(gFinishedCars < TOTAL_VEHICLES) && (gActionNow == -1) ->
      gFrameCounter++;
      /* Check collision */
      bool collision_result;
      collision_msg!0;
      collision_msg?collision_result;
      assert(collision_result == 0);
      /* select the next car to move */
      short temp_action = -1;
      do
        ::temp_action == -1 ->
          select(temp_action : 0 .. TOTAL_VEHICLES - 1);
        ::(temp_action >= 0) && (gCars[temp_action].finish == 1) ->
          select(temp_action : 0 .. TOTAL_VEHICLES - 1);
        :: (temp_action >= 0) && (gCars[temp_action].finish == 0) ->
          break;
      od
      gActionNow = temp_action;
      /* Next frame */
      int i = 0;
      for (i : 0 .. TOTAL_VEHICLES - 1) {
        if
          ::(gCars[i].position >= MAX_ROAD_LENGTH) && (gCars[i].finish != 1) ->
            gCars[i].finish = 1;
            gFinishedCars ++;
          ::else ->
            gCars[i].position = gCars[i].position + gCars[i].speed;
        fi
      }
  od
}

init {
  short i;
  for (i : 0 .. TOTAL_VEHICLES - 1) {
    run VehicleBot(i);
  }
  run AbsService(abs_msg);
  run CheckCollisionService(collision_msg);
  run PrintStateService(print_msg);
  for (i : 0 .. TOTAL_VEHICLES - 1) {
    byte lane;
    gCars[i].id = i;
    select(lane : 0 .. TOTAL_LANES - 1);
    gCars[i].lane = i;
    gCars[i].position = i * (MIN_SAFETY_DISTANCE + 1);
    byte random_speed;
    select(random_speed: 0..1);
    if
      :: random_speed == 0 -> gCars[i].speed = MIN_SPEED;
      :: random_speed == 1 -> gCars[i].speed = MAX_SPEED;
    fi
    gCars[i].finish = 0;
  }
  run GlobalLockStep();
}

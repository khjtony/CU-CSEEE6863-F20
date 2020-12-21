#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define MIN_SPEED 0
// Max speed is in ft/s
#define MAX_SPEED_FPS 88
// Minimum safe distance is 50ft
#define MIN_DISTANCE_FT 50
// Max road length is 500 ft
#define MAX_ROAD_LENGTH 500
// System check collision in next second
#define COLLISION_CURRENT_SECOND 0
// ADS check sollision after two seconds
#define COLLISION_ADS_SECOND 1

#define CASE_ONLY_ME
// #define CASE_ONE_SIDE
// #define CASE_BOTH_SIDE
// #define CASE_MORE_OTHER_VEHICLES
// #define CASE_TEST_COLLISION

int nondet_int();
uint8_t nondet_uchar();

struct Vehicle {
  uint8_t lane;
  int32_t speed;
  int32_t position;
};

uint8_t CheckCollision(const struct Vehicle ego,
    const struct Vehicle* vehicles, const uint8_t max_lanes,
    const uint8_t max_cars, const int32_t seconds) {
  int32_t ego_next_pose = ego.position + ego.speed * seconds;
  int32_t other_next_pose = 0;
  for (uint8_t i = 0; i < max_cars; i++) {
    if (ego.lane != vehicles[i].lane) {
      continue;
    }
    other_next_pose = vehicles[i].position
      + vehicles[i].speed * seconds;
    if (abs(ego_next_pose - other_next_pose) >= MIN_DISTANCE_FT &&
        (ego.position - vehicles[i].position) *
        (ego_next_pose - other_next_pose) > 0) {
      continue;
    } else {
      return 1;
    }
  }
  return 0;
}

struct Vehicle EgoMaxSpeed(const struct Vehicle ego) {
  struct Vehicle local_copy = ego;
  local_copy.speed = MAX_SPEED_FPS;
  return local_copy;
}

struct Vehicle EgoStop(const struct Vehicle ego) {
  struct Vehicle local_copy = ego;
  local_copy.speed = 0;
  return local_copy;
}

struct Vehicle ChangeEgoLaneLeft(const struct Vehicle ego) {
  struct Vehicle local_copy = ego;
  if (local_copy.lane > 0) {
    local_copy.lane--;
  }
  return local_copy;
}

struct Vehicle ChangeEgoLaneRight(const struct Vehicle ego,
    const uint8_t max_lanes) {
  struct Vehicle local_copy = ego;
  if (local_copy.lane < max_lanes - 1) {
    local_copy.lane++;
  }
  return local_copy;
}

struct Vehicle MoveEgo(
    const struct Vehicle ego, const struct Vehicle* vehicles,
    const uint8_t max_lanes, const uint8_t max_cars) {
  if (CheckCollision(
      EgoMaxSpeed(ego), vehicles, max_lanes, max_cars,
      COLLISION_ADS_SECOND) == 0) {
    return EgoMaxSpeed(ego);
  } else if (CheckCollision(
      EgoStop(ego), vehicles, max_lanes, max_cars,
      COLLISION_ADS_SECOND) == 0) {
    return EgoStop(ego);
  } else if (CheckCollision(
      ChangeEgoLaneLeft(ego), vehicles, max_lanes, max_cars,
      COLLISION_ADS_SECOND) == 0) {
    return ChangeEgoLaneLeft(ego);
  } else if (CheckCollision(
      ChangeEgoLaneRight(ego, max_lanes), vehicles, max_lanes, max_cars,
      COLLISION_ADS_SECOND) == 0) {
    return ChangeEgoLaneRight(ego, max_lanes);
  }
  return ego;
}

#if defined CASE_ONLY_ME
#define MAX_CARS 0
#define MAX_LANE_WIDTH 4
int main() {
  struct Vehicle vehicles[MAX_CARS];
  struct Vehicle ego;
  uint8_t collision = 0;

  // Generating ego vehicle.
  ego.lane = nondet_uchar();
  __CPROVER_assume(ego.lane >= 0 && ego.lane < MAX_LANE_WIDTH);
  ego.position = 0;
  ego.speed = nondet_int();
  __CPROVER_assume(ego.speed >= 0
      && ego.speed <= MAX_SPEED_FPS);
  // Check generated vehicle status.
  collision = CheckCollision(ego, vehicles, MAX_LANE_WIDTH, MAX_CARS,
      COLLISION_CURRENT_SECOND);
  __CPROVER_assume(collision == 0);
  ego = MoveEgo(ego, vehicles, MAX_LANE_WIDTH, MAX_CARS);
  collision = CheckCollision(ego, vehicles, MAX_LANE_WIDTH, MAX_CARS,
      COLLISION_ADS_SECOND);
  __CPROVER_assert(collision == 0, "or there will be a collision");
}

#elif (defined CASE_ONE_SIDE)
#define OTHER_MIN_POSITION 100
#define MAX_CARS 5
#define MAX_LANE_WIDTH 4
int main() {
  struct Vehicle vehicles[MAX_CARS];
  struct Vehicle ego;
  uint8_t collision = 0;

  // Generating ego vehicle.
  ego.lane = nondet_uchar();
  __CPROVER_assume(ego.lane >= 0 && ego.lane < MAX_LANE_WIDTH);
  ego.position = 0;
  ego.speed = nondet_int();
  __CPROVER_assume(ego.speed >= 0
      && ego.speed <= MAX_SPEED_FPS);
  // Generating other vehicles.
  for (uint8_t i = 0; i < MAX_CARS; i++) {
    vehicles[i].lane = ego.lane;
    vehicles[i].position = nondet_int();
    __CPROVER_assume(vehicles[i].position >= OTHER_MIN_POSITION
        && vehicles[i].position <= MAX_ROAD_LENGTH);
    vehicles[i].speed = nondet_int();
    __CPROVER_assume(vehicles[i].speed >= 0
        && vehicles[i].speed <= MAX_SPEED_FPS);
  }
  // Check generated vehicle status.
  collision = CheckCollision(ego, vehicles, MAX_LANE_WIDTH, MAX_CARS,
      COLLISION_CURRENT_SECOND);
  __CPROVER_assume(collision == 0);
  ego = MoveEgo(ego, vehicles, MAX_LANE_WIDTH, MAX_CARS);
  collision = CheckCollision(ego, vehicles, MAX_LANE_WIDTH, MAX_CARS,
      COLLISION_ADS_SECOND);
  __CPROVER_assert(collision == 0, "or there will be a collision");
}

#elif (defined CASE_BOTH_SIDE)
#define MAX_CARS 2
#define MAX_LANE_WIDTH 4
int main() {
  struct Vehicle vehicles[MAX_CARS];
  struct Vehicle ego;
  uint8_t collision = 0;
  ego.lane = 0;
  ego.speed = 50;
  ego.position = 100;
  while(1) {    
    // Vehicle[0] is behind ego vehicle
    vehicles[0].lane = 0;
    vehicles[0].position = nondet_int();
    __CPROVER_assume(ego.position < ego.position - 50
        && ego.position < MAX_ROAD_LENGTH);
    vehicles[0].speed = nondet_int();
    __CPROVER_assume(ego.speed >= 0
        && ego.speed < MAX_SPEED_FPS);
    // vehicle[1] is in front of ego vehicle
    vehicles[1].lane = 0;
    vehicles[1].position = nondet_int();
    __CPROVER_assume(ego.position > ego.position + 50
        && ego.position < MAX_ROAD_LENGTH);
    vehicles[1].speed = nondet_int();
    __CPROVER_assume(ego.speed > vehicles[0].speed
       && ego.speed < MAX_SPEED_FPS);
    collision = CheckCollision(ego, vehicles, MAX_LANE_WIDTH, MAX_CARS,
        COLLISION_CURRENT_SECOND);
    __CPROVER_assume(collision == 0);
    ego = MoveEgo(ego, vehicles, MAX_LANE_WIDTH, MAX_CARS);
    collision = CheckCollision(ego, vehicles, MAX_LANE_WIDTH, MAX_CARS,
        COLLISION_ADS_SECOND);
    __CPROVER_assert(collision == 0, "or there will be a collision");
  }
}

#elif (defined CASE_MORE_OTHER_VEHICLES)
#define MAX_CARS 5
#define MAX_LANE_WIDTH 4
int main() {
  struct Vehicle vehicles[MAX_CARS];
  struct Vehicle ego;
  uint8_t collision = 0;
  // Generating ego vehicle.
  ego.lane = nondet_uchar();
  __CPROVER_assume(ego.lane >= 0 && ego.lane < MAX_LANE_WIDTH);
  ego.position = nondet_int();
  __CPROVER_assume(ego.position >= 0 && ego.position < MAX_ROAD_LENGTH);
  ego.speed = nondet_int();
  __CPROVER_assume(ego.speed >= 0 && ego.speed <= MAX_SPEED_FPS);
  // Generating other vehicles.
  for (uint8_t i = 0; i < MAX_CARS; i++) {
    vehicles[i].lane = nondet_uchar();
    __CPROVER_assume(vehicles[i].lane >= 0
        && vehicles[i].lane < MAX_LANE_WIDTH);
    vehicles[i].position = nondet_int();
    __CPROVER_assume(vehicles[i].position >= 0
        && vehicles[i].position <= MAX_ROAD_LENGTH);
    vehicles[i].speed = nondet_int();
    __CPROVER_assume(vehicles[i].speed >= 0
        && vehicles[i].speed <= MAX_SPEED_FPS);
  }
  // Check generated vehicle status.
  collision = CheckCollision(ego, vehicles, MAX_LANE_WIDTH, MAX_CARS,
      COLLISION_CURRENT_SECOND);
  __CPROVER_assume(collision == 0);
  ego = MoveEgo(ego, vehicles, MAX_LANE_WIDTH, MAX_CARS);
  collision = CheckCollision(ego, vehicles, MAX_LANE_WIDTH, MAX_CARS,
      COLLISION_ADS_SECOND);
  __CPROVER_assert(collision == 0, "or there will be a collision");
}

#elif (defined CASE_TEST_COLLISION)
#define MAX_CARS 3
#define MAX_LANE_WIDTH 4
int main() {
  struct Vehicle vehicles[MAX_CARS];
  struct Vehicle ego;
  uint8_t collision = 0;
  // Generating ego vehicle.
  ego.lane = nondet_uchar();
  __CPROVER_assume(ego.lane >= 0 && ego.lane < MAX_LANE_WIDTH);
  ego.position = nondet_int();
  __CPROVER_assume(ego.position >= 0 && ego.position < MAX_ROAD_LENGTH);
  ego.speed = nondet_int();
  __CPROVER_assume(ego.speed >= 0 && ego.speed <= MAX_SPEED_FPS);

  // Generating other vehicles.
  for (uint8_t i = 0; i < MAX_CARS; i++) {
    vehicles[i].lane = nondet_uchar();
    __CPROVER_assume(vehicles[i].lane >= 0
        && vehicles[i].lane < MAX_LANE_WIDTH);
    vehicles[i].position = nondet_int();
    __CPROVER_assume(vehicles[i].position >= 0
        && vehicles[i].position <= MAX_ROAD_LENGTH);
    vehicles[i].speed = nondet_int();
    __CPROVER_assume(vehicles[i].speed >= 0
        && vehicles[i].speed <= MAX_SPEED_FPS);
  }

  // Check generated vehicle status.
  collision = CheckCollision(ego, vehicles, MAX_LANE_WIDTH, MAX_CARS, 
      COLLISION_CURRENT_SECOND);
  __CPROVER_assume(collision == 0);
  ego = MoveEgo(ego, vehicles, MAX_LANE_WIDTH, MAX_CARS);
  collision = CheckCollision(ego, vehicles, MAX_LANE_WIDTH, MAX_CARS,
      COLLISION_ADS_SECOND);
  __CPROVER_assert(collision == 0, "or there will be a collision");
}
#endif

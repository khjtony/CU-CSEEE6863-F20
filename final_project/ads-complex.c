#include <assert.h>
#include <math.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define MIN_SPEED 10
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

#define CBMC
// #define GNUC

// #define CASE_ONLY_ME
// #define CASE_ONE_SIDE
// #define CASE_BOTH_SIDE
// #define CASE_MORE_OTHER_VEHICLES
#define CASE_TEST_COLLISION

#if (defined CBMC)
int nondet_int();
uint8_t nondet_uchar();
#endif  // defined CBMC

enum STResultType {
  STRESULT_BOUNDED = 0,
  STRESULT_UNBOUNDED = 1
};

struct Vehicle {
  uint8_t lane;
  int32_t speed;
  int32_t position;
};

struct STResult {
  // If safe zone is bounded, then speed_score = speed.
  // If safe zone is unbounded, then speed_score = MAX_SPEED_FPS + speed
  enum STResultType type;
  uint8_t ego_lane;
  int32_t speed;
  int32_t range;
};

uint32_t IncrementStackIndex(
    const uint32_t idx, const uint32_t depth_limit) {
  return idx + 1 >= depth_limit ? 0 : idx + 1;
}

struct STResult CompareSTResult(const struct STResult r1,
    const struct STResult r2) {
  if (r1.type != r2.type) {
    return r1.type > r2.type? r1 : r2;
  }
  if (r1.type == STRESULT_BOUNDED) {
    return r1.range > r2.range? r1 : r2;
  }

  if (r1.type == STRESULT_UNBOUNDED) {
    return r1.speed > r2.speed ? r1 : r2;
  }
}

void OccupyTheMap(uint8_t **map,
    const uint32_t row_size, const uint32_t col_size,
    const struct Vehicle vehicle, int8_t direction) {
  // Direction means occupy left or occupy right
  // Notice that we dont need to occupy every cells,
  // just occupying a boundary is enough.
  // https://en.wikipedia.org/wiki/Bresenham%27s_line_algorithm
  const float error = 1.0f / vehicle.speed;
  float acc_error = 0;
  uint32_t s = vehicle.position;
  uint32_t t = 0;
  for (uint32_t s = vehicle.position + direction; s < col_size; s++) {
    if (s >= MAX_ROAD_LENGTH - 1) {
      break;
    } else {
      map[row_size - 1 - t][s] = 1;
    }
    acc_error += error;
    if (acc_error >= 0.5) {
      t++;
      acc_error -= 1.0;
    }
  }
}

struct STResult CalculateSpeedProfile(uint8_t **map,
    const uint32_t row_size, const uint32_t col_size,
    const struct Vehicle ego) {
  float candidate_range = -1;
  float candidate_speed = -1;
  float unbounded_speed = -1;
  float bounded_range = -1;
  struct STResult result;
  result.type = STRESULT_UNBOUNDED;
  result.ego_lane = ego.lane;
  result.speed = -1;
  result.range = -1;
  int32_t t = 0;
  int32_t s = ego.position;
  int32_t current_idx = 0;
  int32_t stack_depth = 1;
  int32_t stack_counter = 1;
  int32_t visited_counter = 0;
  const int32_t MAX_STACK_DEPTH = row_size * col_size;
  int32_t stack_row[MAX_STACK_DEPTH];
  int32_t stack_col[MAX_STACK_DEPTH];
  stack_row[current_idx] = row_size - 1;
  stack_col[current_idx] = s;
  int32_t temp_row = 0;
  int32_t temp_col = 0;
  // In this case we only need to search to right and up.
  while(visited_counter < stack_counter) {
    temp_row = stack_row[current_idx];
    temp_col = stack_col[current_idx];
    current_idx = IncrementStackIndex(current_idx, MAX_STACK_DEPTH);
    visited_counter++;
    if (map[temp_row][temp_col] == 0) {
      // Free
      candidate_speed = (temp_col - ego.position) / (row_size - temp_row);
      if ((temp_row <= 0 || temp_col >= col_size - 1) &&
          candidate_speed < MIN_SPEED) {
        // Manual limite the smalled speed.
        map[temp_row][temp_col] = 1;
        continue;
      }
      candidate_range = sqrt(
          (row_size - temp_row) * (row_size - temp_row)
          + (temp_col - ego.position) * (temp_col - ego.position));
      candidate_speed = 1.0 * (temp_col - ego.position) /
          (row_size - 1 - temp_row);
      if (temp_col >= MAX_ROAD_LENGTH - 1
          && candidate_speed > unbounded_speed) {
        // Found unbounded. Look at speed.
        unbounded_speed = candidate_speed;
        result.speed = (int)round(candidate_speed);
        result.range = (int)round(candidate_range);
        result.type = STRESULT_UNBOUNDED;
      } else if (temp_col < MAX_ROAD_LENGTH - 1 &&
          candidate_range > bounded_range &&
          result.type == STRESULT_BOUNDED) {
        // new bounded frontier. look at travel range.
        bounded_range = candidate_range;
        result.speed = (int)round(candidate_speed);
        result.range = (int)round(candidate_range);
      }
      // Search for right cell and upper cell;
      if (temp_col + 1 < col_size) {
        stack_row[stack_depth] = temp_row;
        stack_col[stack_depth] = temp_col + 1;
        stack_depth = IncrementStackIndex(stack_depth, MAX_STACK_DEPTH);
        stack_counter++;
      }
      if (temp_row - 1 >= 0) {
        stack_row[stack_depth] = temp_row - 1;
        stack_col[stack_depth] = temp_col;
        stack_depth = IncrementStackIndex(stack_depth, MAX_STACK_DEPTH);
        stack_counter++;
      }
      // visited cell.
      map[temp_row][temp_col] = 1;
    }
  }
  printf("CalculateSpeedProfile finihsed, speed: %d, range: %d\n",
      result.speed, result.range);
  return result;
}

// During each STGraphSolver we only calculate the result
// for the current lane.
// Init STResult. speed == -1 means no result.
// Creating occupency map;
// Indexing order is map[row][col];
// Row aligns to y-axis(time)
// Col aligns to x-axis(travel distance)
struct STResult STGraphSolver(const struct Vehicle ego,
    const struct Vehicle* vehicles,
    const uint8_t max_lanes,
    const uint8_t max_cars) {
  uint8_t **occupency_map;
  const uint32_t ROW_SIZE = MAX_ROAD_LENGTH / MIN_SPEED;
  const uint32_t COL_SIZE = MAX_ROAD_LENGTH;
  occupency_map = (uint8_t**)malloc(ROW_SIZE * sizeof(uint8_t*));
  for (uint32_t i = 0; i < ROW_SIZE; i++) {
    occupency_map[i] = (uint8_t*)calloc(COL_SIZE, sizeof(uint8_t));
  }
  // Filling the cell.
  struct Vehicle dummy_ego = ego;
  dummy_ego.speed = MAX_SPEED_FPS;
  OccupyTheMap(occupency_map, ROW_SIZE, COL_SIZE, dummy_ego, 1);
  for (uint8_t i = 0; i < max_cars; i++) {
    if (vehicles[i].lane == ego.lane) {
      if (vehicles[i].position <= ego.position) {
        // Have 1 second safety range.
        struct Vehicle dummy_car = vehicles[i];
        dummy_car.position += dummy_car.speed;
        OccupyTheMap(occupency_map, ROW_SIZE, COL_SIZE, dummy_car, -1);
      } else {
        // Have 1 second safety range.
        struct Vehicle dummy_car = vehicles[i];
        dummy_car.position -= dummy_car.speed;
        OccupyTheMap(occupency_map, ROW_SIZE, COL_SIZE, dummy_car, 1);
      }
    }
  }
  // printf("Map size: [%d, %d]\n", ROW_SIZE, COL_SIZE);
  // for (uint32_t c = 0; c < COL_SIZE; c++) {
  //   for (uint32_t r = 0; r < ROW_SIZE; r++) {
  //     printf("%d ", occupency_map[ROW_SIZE - 1 - r][c]);
  //   }
  //  printf("\n");
  // }
  struct STResult result = CalculateSpeedProfile(
      occupency_map, ROW_SIZE, COL_SIZE, ego);
  // Find the result.
  // free
  for (uint32_t i = 0; i < ROW_SIZE; i++) {
    free(occupency_map[i]);
  }
  free(occupency_map);
  return result;
}

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
  struct STResult best_st_result;
  struct STResult st_result;
  struct Vehicle dummy_ego = ego;
  // Current lane.
  best_st_result = STGraphSolver(ego, vehicles, max_lanes, max_cars);
  dummy_ego = ChangeEgoLaneLeft(ego);
  st_result = STGraphSolver(dummy_ego, vehicles, max_lanes, max_cars);
  if (st_result.speed > best_st_result.speed) {
    best_st_result = st_result;
  }
  best_st_result = CompareSTResult(best_st_result, st_result);
  dummy_ego = ChangeEgoLaneRight(ego, max_lanes);
  st_result = STGraphSolver(dummy_ego, vehicles, max_lanes, max_cars);
  best_st_result = CompareSTResult(best_st_result, st_result);
  dummy_ego = ego;
  dummy_ego.speed = best_st_result.speed;
  return dummy_ego;
}

#if (defined CASE_ONLY_ME) && (defined CBMC)
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
  __CPROVER_assume(ego.speed >= MIN_SPEED
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

#elif (defined CASE_ONE_SIDE) && (defined CBMC)
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
  __CPROVER_assume(ego.speed >= MIN_SPEED
      && ego.speed <= MAX_SPEED_FPS);
  // Generating other vehicles.
  for (uint8_t i = 0; i < MAX_CARS; i++) {
    vehicles[i].lane = ego.lane;
    vehicles[i].position = nondet_int();
    __CPROVER_assume(vehicles[i].position >= OTHER_MIN_POSITION
        && vehicles[i].position <= MAX_ROAD_LENGTH);
    vehicles[i].speed = nondet_int();
    __CPROVER_assume(vehicles[i].speed >= MIN_SPEED
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

#elif (defined CASE_BOTH_SIDE) && (defined CBMC)
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
    __CPROVER_assume(ego.speed >= MIN_SPEED
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

#elif (defined CASE_MORE_OTHER_VEHICLES) && (defined CBMC)
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
  __CPROVER_assume(ego.speed >= MIN_SPEED && ego.speed <= MAX_SPEED_FPS);
  // Generating other vehicles.
  for (uint8_t i = 0; i < MAX_CARS; i++) {
    vehicles[i].lane = nondet_uchar();
    __CPROVER_assume(vehicles[i].lane >= 0
        && vehicles[i].lane < MAX_LANE_WIDTH);
    vehicles[i].position = nondet_int();
    __CPROVER_assume(vehicles[i].position >= 0
        && vehicles[i].position <= MAX_ROAD_LENGTH);
    vehicles[i].speed = nondet_int();
    __CPROVER_assume(vehicles[i].speed >= MIN_SPEED
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

#elif (defined CASE_TEST_COLLISION) && (defined CBMC)
#define MAX_CARS 3
#define MAX_LANE_WIDTH 4
int main() {
  struct Vehicle vehicles[MAX_CARS];
  struct Vehicle ego;
  uint8_t collision = 0;
  // Generating ego vehicle.
  ego.lane = 0;
  ego.position = 150;
  ego.speed = 30;

  // Generating other vehicles.
  vehicles[0].lane = 0;
  vehicles[0].position = 90;
  vehicles[0].speed = 60;
  vehicles[1].lane = 1;
  vehicles[1].position = 150;
  vehicles[1].speed = 30;
  vehicles[2].lane = 10;
  vehicles[2].position = 210;
  vehicles[2].speed = 10;

  // Check generated vehicle status.
  collision = CheckCollision(ego, vehicles, MAX_LANE_WIDTH, MAX_CARS, 
      COLLISION_CURRENT_SECOND);
  __CPROVER_assume(collision == 0);
  ego = MoveEgo(ego, vehicles, MAX_LANE_WIDTH, MAX_CARS);
  collision = CheckCollision(ego, vehicles, MAX_LANE_WIDTH, MAX_CARS,
      COLLISION_ADS_SECOND);
  __CPROVER_assert(collision == 0, "or there will be a collision");
}

#elif (defined GNUC)
#define MAX_CARS 2
#define MAX_LANE_WIDTH 4
int main() {
  struct Vehicle vehicles[MAX_CARS];
  struct Vehicle ego;
  uint8_t collision = 0;
  // Generating ego vehicle.
  ego.lane = 0;
  ego.position = 150;
  ego.speed = 30;

  // Generating other vehicles.
  vehicles[0].lane = 0;
  vehicles[0].position = 90;
  vehicles[0].speed = 60;
  vehicles[1].lane = 1;
  vehicles[1].position = 150;
  vehicles[1].speed = 30;
  vehicles[2].lane = 10;
  vehicles[2].position = 210;
  vehicles[2].speed = 10;

  // Check generated vehicle status.
  collision = CheckCollision(ego, vehicles, MAX_LANE_WIDTH, MAX_CARS, 
      COLLISION_CURRENT_SECOND);
  ego = MoveEgo(ego, vehicles, MAX_LANE_WIDTH, MAX_CARS);
  collision = CheckCollision(ego, vehicles, MAX_LANE_WIDTH, MAX_CARS,
      COLLISION_ADS_SECOND);
  assert(collision == 0);
}
#endif
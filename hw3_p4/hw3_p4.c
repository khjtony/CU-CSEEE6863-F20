// CSEEE6863 HW3 P4
// Oct.30 2020
// Hengjiu Kang(hk3120)
#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#define MAP_SIZE 6
// #define DEBUG_1
// #define DEBUG_2
// #define DEBUG_3

enum MoveAction {
  MoveStall = 0,
  MoveForward = 1,
  MoveBackward = -1
};

enum VehicleDirection {
  VehicleHorizontal = 1,
  VehicleVertial = 0
};

struct Vector2i {
  int8_t x;
  int8_t y;
};

struct Vehicle {
  uint8_t id;
  struct Vector2i body[2];
  enum VehicleDirection direction;
};

enum MoveResultStatus {
  MoveSuccess = 0,
  MoveCollision = 1,
  MoveInvalidArgument = 2,
  MoveOutOfBound = 3,
  MoveFinished = 4
};

struct MoveResult {
  enum MoveResultStatus status;
  uint8_t collision_id;
};

extern inline bool isSamePoint(const struct Vector2i p1,
    const struct Vector2i p2) {
  if (p1.x == p2.x && p1.y == p2.y) {
    return true;
  } else {
    return false;
  }
}

extern inline void PrintVehicleConfig(
    struct Vehicle* vehicles, uint8_t vehicle_count) {
  printf("Current config: ");
  for (uint8_t i = 0; i < vehicle_count; i++) {
    printf("%d: (%d, %d), (%d, %d) \t",
        i,
        vehicles[i].body[0].x,
        vehicles[i].body[0].y,
        vehicles[i].body[1].x,
        vehicles[i].body[1].y);
  }
  printf("\n");
}

struct Vehicle GenerateVehicle(
    const struct Vector2i head, const struct Vector2i tail, const uint8_t id) {
  struct Vehicle vehicle;
  vehicle.id = id;
  vehicle.body[0] = head;
  vehicle.body[1] = tail;
  if (head.x == tail.x) {
    vehicle.direction = VehicleVertial;
  } else {
    vehicle.direction = VehicleHorizontal;
  }
  return vehicle;
}

struct MoveResult OneMove(struct Vehicle* vehicles,
    const uint8_t vehicle_count, const uint8_t move_id,
    const enum MoveAction move, const bool dry_run) {
  struct MoveResult result;
  result.status = MoveSuccess;
  // Sanity check.
  if (NULL == vehicles || vehicle_count <= 0
      || move_id >= vehicle_count) {
    result.status = MoveInvalidArgument;
    return result;
  }

  // Create a dummy move
  struct Vehicle dummy_vehicle = vehicles[move_id];
  dummy_vehicle.body[0].x += (int8_t)move * (int8_t)dummy_vehicle.direction;
  dummy_vehicle.body[0].y += (int8_t)move
      * (1 - (int8_t)dummy_vehicle.direction);
  dummy_vehicle.body[1].x += (int8_t)move * (int8_t)dummy_vehicle.direction;
  dummy_vehicle.body[1].y += (int8_t)move
      * (1 - (int8_t)dummy_vehicle.direction);
  
  #ifdef DEBUG_2
    printf("Vehicle at %d:(%d, %d), try to move to (%d, %d)\n",
        move_id,
        vehicles[move_id].body[0].x,
        vehicles[move_id].body[0].y,
        dummy_vehicle.body[0].x,
        dummy_vehicle.body[0].y);
  #endif
 
  // Check collision
  for (uint8_t i = 0;i < vehicle_count; i++) {
    if (i == move_id) {
      continue;
    }
    if (isSamePoint(dummy_vehicle.body[0], vehicles[i].body[0])
        || isSamePoint(dummy_vehicle.body[0], vehicles[i].body[1])
        || isSamePoint(dummy_vehicle.body[1], vehicles[i].body[0])
        || isSamePoint(dummy_vehicle.body[1], vehicles[i].body[1])) {
      // Has collision
      result.status = MoveCollision;
      result.collision_id = i;

      #ifdef DEBUG_2
      printf(
          "Vehicle at %d:(%d, %d, %d, %d), collide with %d:(%d, %d, %d, %d)\n",
          move_id,
          dummy_vehicle.body[0].x,
          dummy_vehicle.body[0].y,
          dummy_vehicle.body[1].x,
          dummy_vehicle.body[1].y,
          i,
          vehicles[i].body[0].x,
          vehicles[i].body[0].y,
          vehicles[i].body[1].x,
          vehicles[i].body[1].y);
      #endif
      break;
    }
  }
  // Check out of bound.
  if (dummy_vehicle.body[0].x < 0 || dummy_vehicle.body[0].x >= MAP_SIZE
      || dummy_vehicle.body[0].y < 0 || dummy_vehicle.body[0].y >= MAP_SIZE
      || dummy_vehicle.body[1].x < 0 || dummy_vehicle.body[1].x >= MAP_SIZE
      || dummy_vehicle.body[1].x < 0 || dummy_vehicle.body[1].y >= MAP_SIZE) {
    result.status = MoveOutOfBound;
  }

  if (result.status == MoveSuccess && dry_run == false) {
    // Real move.
    vehicles[move_id] = dummy_vehicle;
  }
  return result;
}

bool isVehicleConfigVisited(
    struct Vehicle* current_vehicle_config,
    const uint8_t vehicle_count,
    struct Vehicle** total_vehicles,
    const uint32_t total_vehicle_size) {
  bool visited = true;
  for (uint32_t i = 0; i < total_vehicle_size; i++) {
    visited = true;
    for (uint8_t j = 0; j < vehicle_count; j++) {
      if (current_vehicle_config[j].body[0].x
          != total_vehicles[i][j].body[0].x
          || current_vehicle_config[j].body[0].y
          != total_vehicles[i][j].body[0].y
          || current_vehicle_config[j].body[1].x
          != total_vehicles[i][j].body[1].x
          || current_vehicle_config[j].body[1].y
          != total_vehicles[i][j].body[1].y) {
        visited = false;
        break;
      }
    }
    if (visited == true) {
      return visited;
    }
  }
  return false;
}

bool isRushHourFinished(
    struct Vehicle target_pos,
    struct Vehicle** total_vehicles,
    const uint8_t vehicle_count,
    const uint32_t total_vehicle_size) {
  bool result = false;
  for (uint32_t i = 0; i < total_vehicle_size; i++) {
    if (isSamePoint(target_pos.body[0],
        (total_vehicles[i][0].body[0]))
        || isSamePoint(target_pos.body[0],
        (total_vehicles[i][0].body[1]))
        || isSamePoint(target_pos.body[1],
        (total_vehicles[i][0].body[0]))
        || isSamePoint(target_pos.body[1],
        (total_vehicles[i][0].body[1]))) {
      result = true;
    }
  } 
  assert(result == true);
  return result;
}

void RushHourBuildBFSMap(
    struct Vehicle** total_vehicles,
    const uint32_t current_vehicle_config_idx,
    const uint8_t vehicle_count,
    uint32_t* total_vehicle_size,
    const uint32_t total_vehicle_capacity) {
  struct MoveResult result;
  result.status = MoveSuccess;
  struct Vehicle* current_vehicle_config;
  const size_t kSizeOfOneConfig = sizeof(struct Vehicle) * vehicle_count;
  current_vehicle_config = (struct Vehicle*)malloc(
      kSizeOfOneConfig);
  for (uint8_t i = 0; i < vehicle_count; i++) {
    // Move forward
    memcpy(current_vehicle_config,
        total_vehicles[current_vehicle_config_idx],
        kSizeOfOneConfig);
    result = OneMove(current_vehicle_config,
        vehicle_count, i, MoveForward, false);
    if (result.status == MoveSuccess
        && !isVehicleConfigVisited(current_vehicle_config, vehicle_count,
        total_vehicles, *total_vehicle_size)) {
      // Save current config.
      PrintVehicleConfig(current_vehicle_config, vehicle_count);
      assert(*total_vehicle_size < total_vehicle_capacity);
      total_vehicles[*total_vehicle_size] = (struct Vehicle*)malloc(
        kSizeOfOneConfig);
      memcpy(total_vehicles[*total_vehicle_size],
        current_vehicle_config,
        kSizeOfOneConfig);
      (*total_vehicle_size)++;
    } else {
      #ifdef DEBUG_2
      printf("OneMove failed with: %d, %d collision with %d\n",
        (int)result.status, i, result.collision_id);
      #endif
      ;
    }
    // Move backward.
    memcpy(current_vehicle_config,
        total_vehicles[current_vehicle_config_idx],
        kSizeOfOneConfig);
    result = OneMove(current_vehicle_config,
        vehicle_count, i, MoveBackward, false);
    if (result.status == MoveSuccess
        && !isVehicleConfigVisited(current_vehicle_config, vehicle_count,
        total_vehicles, *total_vehicle_size)) {
      // Save current config.
      PrintVehicleConfig(current_vehicle_config, vehicle_count);
      assert(*total_vehicle_size < total_vehicle_capacity);
      total_vehicles[*total_vehicle_size] = (struct Vehicle*)malloc(
        kSizeOfOneConfig);
      memcpy(total_vehicles[*total_vehicle_size],
        current_vehicle_config,
        kSizeOfOneConfig);
      (*total_vehicle_size)++;
    }
  }
  free(current_vehicle_config);
}

int main(int argc, char** argv) {
  // Const variables.
  struct Vector2i kStartPosition = {.x = 0, .y = MAP_SIZE / 2};
  struct Vector2i kStopPosition = {.x = MAP_SIZE, .y = MAP_SIZE / 2};
  const uint32_t kTotalConfigSize = 100;
  const uint8_t kVehicleCount = 4;

  // Construct map.
  struct Vehicle** total_vehicles =
      (struct Vehicle**)malloc(sizeof(struct Vehicle*) * kTotalConfigSize);
  total_vehicles[0] = (struct Vehicle*)malloc(
      sizeof(struct Vehicle) * kVehicleCount);

  total_vehicles[0][0] = GenerateVehicle((struct Vector2i){.x = 1, .y = 2},
      (struct Vector2i){.x = 0, .y = 2}, 0);
  total_vehicles[0][1] = GenerateVehicle((struct Vector2i){.x = 2, .y = 1},
      (struct Vector2i){.x = 2, .y = 0}, 1);
  total_vehicles[0][2] = GenerateVehicle((struct Vector2i){.x = 2, .y = 5},
      (struct Vector2i){.x = 2, .y = 4}, 2);
  total_vehicles[0][2] = GenerateVehicle((struct Vector2i){.x = 2, .y = 3},
      (struct Vector2i){.x = 2, .y = 2}, 3);

  struct Vehicle target_pos = GenerateVehicle(kStopPosition, kStopPosition, 0);
  
  // Build configuration maps using BFS.
  uint32_t current_vehicle_config_idx = 0;
  uint32_t total_vehicle_config_size = 1;
  while(current_vehicle_config_idx < total_vehicle_config_size) {
    RushHourBuildBFSMap(
        total_vehicles,
        current_vehicle_config_idx,
        kVehicleCount,
        &total_vehicle_config_size,
        kTotalConfigSize); 
    current_vehicle_config_idx++;
  }
  printf("Total config size: %d\n", total_vehicle_config_size);

  // Check result
  if(isRushHourFinished(target_pos,
      total_vehicles, kVehicleCount, total_vehicle_config_size)) {
    printf("This init configure has solution\n");
  } else {
    printf("This init configure does not have solution\n");
  }
  return 0;
}
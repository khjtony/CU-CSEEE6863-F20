#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <assert.h>

struct Vector2i {
  int x;
  int y;
};

struct Vehicle {
  uint8_t id;
  struct Vector2i coordinate[2];
  bool horizontal;
};

bool module_init = false;
void move_a_car(idx, direction) {
  struct Vehicle vehicles[3];
  if (!module_init) {
    // init 
    vehicles[0].coordinate[0] = (struct Vector2i){.x = 2, .y = 3};
    vehicles[0].coordinate[1] = (struct Vector2i){.x = 2, .y = 2};
    // ...
    module_init = true;
  }
  // try to move a car
  vehicles[0].coordinate[0].x++;
  // update_coordiate
  // check if there is collison
  // check if car is out of board in the next run
  // if nothing bad happend
  assert(!(vehicles[0].coordinate[0].x == 6
      && vehicles[0].coordinate[1].y == 3));
}
# CU-CSEEE6863-F20
This is repo for the class CSEEE6863(Formal verification) in the Fall 2020 in Columbia University. 

## Team
* Erilda Danaj (ed2917_at_columbia_edu)
* Hengjiu Kang (hk3120_at_columbia_edu)

## Repo structure
* final_project: our class final project.
* CSEEE6863F20_final_slides.pdf: our presentation for the final project.
* NOT_FINISHED_ADS_written_report.pdf: our written version of final project. Notice that it is the unfinished work that does not reflect our test on the SPIN.

## System pre-requisite
* Latest version of [CBMC](https://www.cprover.org/cbmc/)
* Latest version of [SPIN](http://spinroot.com/spin/whatispin.html)

## How to run the code
There are three parts of our work:
1. Autonomous Driving System(ADS) intuitive model using CMBC
2. ADS intuitive model using SPIN
3. ADS complex model using CBMC
  
### ADS intuitive model using CBMC
Source code is /final_project/ads-standard.c. You can use
```bash
cbmc ./ads-standard.c --stop-on-fail --trace --unwind 10`
```
to check the model.  
Notice that in the source file we have different init state setup:  
```C
#define CASE_ONLY_ME
// #define CASE_ONE_SIDE
// #define CASE_BOTH_SIDE
// #define CASE_MORE_OTHER_VEHICLES
// #define CASE_TEST_COLLISION
```
you can uncomment one of these lines to change the init state.  
CBMC should provides counter examples when testing with **CASE_MORE_OTHER_VEHICLES** and **CASE_TEST_COLLISION**

### ADS intuitive model using SPIN
Source code is /final_project/multiple_vehicle.pml. You can check the model using  
```bash
spin -g -TC -u50000 ./multiple_vehicle.pml
```
Notice that currently I fixed the init state with total vehicles equals to 4 and total lanes equals to 4.  
You can change line 227 to  
```
gCars[i].lane = lane;
```
to assign random lane to each vehicle.  
After changing the lane assignment, this model should violate property asserted at line 189.

### ADS complex model using CBMC
Source code is /final_project/ads-complex.c. You can check this model using
```bash
cbmc ./ads-complex.c --stop-on-fail --trace --unwind 10
```
This model has macro defiend in the line 20 to change the compiler.  
If we uncomment line 20, then we can use cbmc to check the model.  
If we uncomment line 21 and comment line 20, this code should be compiled by gnuc compiler and gives out result per different cases defined from line 23 to line 27 using RT graph method.

# Finished and unfinished work
## ADS intuitive model using CBMC
### Finished work
* Proving that this model works in certain scenarios.
* Proving that this model is not universal safe.
* Proving that CBMC can help us prove our prove.
* Using nondet_int() and nondet_float() to define input values to the model(syste).
### Unfinished
* Did not bring liveness properties into design.
  
## ADS intuitive model using SPIN
### Finished work
* Porting ADS intuitive model from C to promela and modify the architecture in promela style.
* Proving that this model works in certain scenarios.
* Proving that this model is not universal safe.
### Unfinished
* The code may have bug because the natively concurrent property of Promela is very different than C/C++.
* I manually assign the position of vehicles to make sure that vehicle do not collide at very beginning, because generating a safe init case purely using selec() semantic is slow.
* I should discover more properties and use LTL language to specify the properties instead of using assert().
* I might need to modeling ADS intuitive model in a more abstracitve way.

## ADS complex model using CBMC
### Finished work
* Proving that this model works in certain scenarios.
* Proving that this model is not universal safe.
* Compiled code using goto-cc to make sure that it does not have compile error.
* Compiled code using GNUC to make sure that this code runs without obvious bugs.
* Proving that RT graph can provide answer in certain scenarios.
### Unifinished work
* Did not use CBMC to check that RT graph solver itself is safe.
* Did not use CBMC to check more complex cases due to taking too long.
* Did not introduce liveness properties.
 #include <stdio.h>


int C1D=10,C2D=15, C3D=23, EgoD=0;
int C1S=10,C2S=20,C3S=25, EgoS=0;
int t=1;

int runAtMaximumSpeed(egos){
    egos = 60;
    printf("Accelerating at %d\n", egos);
}

int c1getDistance(int dis, int sp, int t){
    sleep(t);
    dis = (sp*t);
    printf("car 1 is a t %d feet\n",dis);
    return dis;
}

int c2getDistance(int dis, int sp, int t){
    sleep(t);
    dis = (sp*t);
    printf("car 2 is at %d feet\n",dis);
    return dis;
}
int c3getDistance(int dis, int sp, int t){
    sleep(t);
    dis = (sp*t);
    printf("car 3 is at %d feet\n",dis);
    return dis;
}
int egogetDistance(int dis, int sp, int t){
    sleep(t);
    dis = (sp*t);
    printf("Ego is at %d feet\n",dis);
    return dis;
}

int start(int* CS){
    printf("Starting at %d\n",*CS);

}
int changeToLeftLane(){
    printf("Changing to Left Lane: Overtaking Car 2\n");
}
int changeToRightLane(){
    printf("Changing to Right Lane: Overtaking Car 3\n");
}
int stop(){
    printf("Decelerating: Distance less than 50\n");
}

int main(){

    start(&C1S);
    start(&C2S);
    start(&C3S);
    start(&EgoS);

    while(t < 36){
        printf("-----------------Second %d--------------------\n", t);
        EgoS = EgoS + 5;

        int c1d = c1getDistance(C1D,C1S,t);
        int c2d = c2getDistance(C2D,C2S,t);
        int c3d = c3getDistance(C3D,C3S,t);
        int egod = egogetDistance(EgoD,EgoS,t);

        int rC1E = egod-c1d;
        int rC2E = egod-c2d;
        int rC3E = egod-c3d;

        if(rC1E>50){
            if(rC2E > 50 && rC2E<100){
                runAtMaximumSpeed(EgoS);
                changeToLeftLane();

            }

        }else if(rC3E > 50){
            runAtMaximumSpeed();
            changeToRightLane();
        }else {
            stop();
        }

        t++;

        //printf("-----------------Second %d--------------------\n", t);

    }





}

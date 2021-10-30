#include <iostream>
extern "C"{
    int entry();
}
int main(int argc,char** argv){
    int a = entry();
    std::cout<<"\nReturn: "<<a;
}
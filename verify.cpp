#include <iostream>
#include <stdlib.h>
#include <string.h>
#include <sstream>
#include <stdio.h>
using namespace std;

string split(string filename);
void printUsage();
void compile(string filename);
void opt(string name, int b, double p, int m, char* f, char* e);

int main(int argc, char* argv[]){
    if(argc < 6){
        printUsage();
        exit(1);
    }
  
    //Process the flags
    string filename(argv[1]);
    cout << "<" << filename << "> \n";
    char* expression = NULL;
    char* func = NULL;
    int bound=0;
    double precision=0.01;
    int mode = 0;
    bool mode_a=false;
    bool mode_d=false;
    for(int i = 2; i < argc; i ++){
        if(argv[i][0] == '-' && strlen(argv[i]) == 2){
            if(argv[i][1] == 'f'){
                func = argv[i+1]; 
                i ++;
            }
            else if(argv[i][1] == 'b'){
                bound = atoi(argv[i+1]);
                i ++;
            }
            else if(argv[i][1] == 'p'){
                precision = atof(argv[i+1]);
                i ++;
            }
            else if(argv[i][1] == 'e'){
                expression = argv[i+1];
                i ++;
            }
            else if(argv[i][1] == 'a'){
                mode_a = true;
                i ++;
            }
            else if(argv[i][1] == 'd'){
                mode_d = true;
                i ++;
            }
            else{
                printUsage();
                exit(1); 
            }
        }
    }
    if(func==NULL||bound==0){
        printUsage();
        exit(1);
    }
    if (mode_a&&!mode_d)
        mode = 1;
    else if(mode_d&&!mode_a)
        mode = 2;

    string name = split(filename);
    compile(name);
    opt(name, bound, precision, mode, func, expression);
    return 0;
}

void printUsage(){
    cout << "Usage: verify filename -f <func> -b <bound> [-options]" << endl;
    cout << "[-options]:" << endl;
    cout<<"\t-p <precision>\t\tset precision of smt solver"<<endl;
    cout<<"\t-a\t\tset mode in which BRICK check assert only"<<endl;
    cout<<"\t-d\t\tset mode in which BRICK check domain error only"<<endl;
}

void compile(string name){
    string cflags = "-emit-llvm -g ";
    string command = "clang -c " + cflags + name + ".c " + "-o "+ name + ".bc";
    system(command.c_str());
    return;
}

// convert integer to char, but only up to 256 digits!
string inttostring(const int i)
{
  char chr[256];
  string str;
  sprintf(chr,"%i",i);
  str=chr;
  return str;
}
 // convert integer to char, but only up to 256 digits!
string doubletostring(const double d)
{
  char chr[256];
  string str;
  sprintf(chr,"%g",d);
  str=chr;
  return str;
}

void opt(string name, int b, double p, int m, char* f, char* e){
    string bound = "-bound=" + inttostring(b);
    string precision = "-pre=" + doubletostring(p);
    string mode = "-mode=" + inttostring(m);
    string func = "-func=" + string(f);
    string expr = "";
    if(e != NULL)
        expr += "-expression=" + string(e);
    string command = "opt -load buildCFG.so -buildCFG "+bound+" "+precision+" "+mode+" "+func+" "+expr+"<"+name+".bc>"+name+"buildCFG.bc";
    cout << command<<endl;
    system(command.c_str());
}
string split(string filename){
    int i;
    for(i = 0; i < filename.length(); i ++){
        if(filename.at(i) == '.')
            break;
    }
    return filename.substr(0,i);
}

#ifndef _verification_h
#define _verification_h
#include "CFG.h"
#include "general.h"
#include <stdio.h>
#include <cstdlib>
#include <sstream>
#include <cstring>
#include "dreal.h"
#include <fstream>
#include "math.h"

extern int smt2set_in   (FILE *);
extern int smt2parse    ();
extern int m_argc;
extern char ** m_argv;


class IndexPair{
public:
	int start;
	int end;
	IndexPair(int _start,int _end):start(_start),end(_end){}
	bool contain(IndexPair& index){return start>=index.start && end<=index.end;}
	void print(){errs()<<"("<<start<<","<<end<<")";}
};


class VarTable{
private:
	dreal_context &ctx;
	int var_num;
	int alloca_num;
	map<int, double> varVal;
	map<int, int> alias;
	vector<dreal_expr> x;
	map<int, int> exprMap;
	CFG *cfg;
public:
	VarTable(dreal_context &c, CFG *ha):ctx(c), cfg(ha){
		int inputID=0;
		var_num = 0;
		alloca_num = 0;
		for(int i=0; i<cfg->mainInput.size();i++)
			errs()<<"VarTable initial "<<cfg->mainInput[i]<<"\t"<<cfg->variableList[cfg->mainInput[i]].name<<"\n";
		for(unsigned i=0;i<cfg->variableList.size();i++)
		{
			Variable var =  cfg->variableList[i];
			VarType type = var.type;

			if(inputID<cfg->mainInput.size()&&cfg->mainInput[inputID]==(int)i){

				if(type==FP)
					x.push_back(dreal_mk_real_var(ctx, var.name.c_str(), -100.0, 100.0));
//				x.push_back(dreal_mk_unbounded_real_var(ctx, var.name.c_str()));
				else if(type==INT)
					x.push_back(dreal_mk_int_var(ctx, var.name.c_str(), -100.0, 100.0));
				exprMap[i] = var_num;
			    double const x_lb = dreal_get_lb(ctx, x[var_num]);
			    double const x_ub = dreal_get_ub(ctx, x[var_num]);
			    errs()<<var.name<<" = ["<<x_lb<<", "<<x_ub<<"]\n";
				inputID++;
				var_num++;
			}
			else if(type==FP){
				x.push_back(dreal_mk_unbounded_real_var(ctx, var.name.c_str()));
				exprMap[i] = var_num; 
				var_num++;
			}
			else if(type==INT){
				x.push_back(dreal_mk_unbounded_int_var(ctx, var.name.c_str()));
				exprMap[i] = var_num; 
				var_num++;
			}
		}
	}

	~VarTable(){varVal.clear();alias.clear();var_num=0;alloca_num=0;cfg=NULL;}

	void setX(int ID, int time, VarType type){
		int ID2 = exprMap[ID];
		if(type==FP)
			x[ID2] = dreal_mk_unbounded_real_var(ctx, (cfg->variableList[ID].name+"_"+int2string(time)).c_str());
		else if(type==INT)
			x[ID2] = dreal_mk_unbounded_int_var(ctx, (cfg->variableList[ID].name+"_"+int2string(time)).c_str());
		else
			errs()<<"SetX error 10086!!\n";
	}
	int alloca(){
		alias[++alloca_num] = -2;
		return alloca_num;
	}
	void setAlias(int ID1, int ID2){
		alias[ID1] = ID2;
	}
	void setVal(int ID, double val){
		varVal[ID] = val;
	}
	
	int getNum(){
		return var_num;	
	}
	
	dreal_expr getX(int ID){
		int ID2 = exprMap[ID];
		return x[ID2];
	}
	
	int getAlias(int ID){
		int count = alias.count(ID);
		int aliasID;
		if(count){
			aliasID = alias[ID];
			if(aliasID==-2)
				errs()<<"GetAlias error1 "<<ID<<"\t"<<cfg->variableList[ID]<<"\n";
			return aliasID;
		}
		else{
			errs()<<"GetAlias error2 "<<ID<<"\t"<<cfg->variableList[ID]<<"\n";
			return -1;
		}
	}
	bool getVal(int ID, double &v){
		int count = varVal.count(ID);
		if(count){
			v = varVal[ID];
			return true;
		}
		else{
			return false;
		}
	}
	map<int, double> getValmap(){
	   	return varVal;
	}
	map<int, int> getAliasmap(){
	   	return alias;
	}
	CFG *getCFG(){
		return cfg;
	}
};

class Verification{

	string smt;
	dreal_context ctx;
    VarTable *table;
	double time;
	double precision;

	dreal_expr getExpr(Variable *v, bool &treat, double &val, VarTable *table);
	dreal_expr dreal_mk_AND(dreal_context ctx, dreal_expr y, dreal_expr z, string name, unsigned num);
	dreal_expr dreal_mk_NAND(dreal_context ctx, dreal_expr y, dreal_expr z, string name, unsigned num);
	dreal_expr dreal_mk_OR(dreal_context ctx, dreal_expr y, dreal_expr z, string name, unsigned num);
	dreal_expr dreal_mk_XOR(dreal_context ctx, dreal_expr y, dreal_expr z, string name, unsigned num);
	dreal_expr dreal_mk_SREM(dreal_context ctx, dreal_expr y, dreal_expr z, string name);
	dreal_expr dreal_mk_ASHR(dreal_context ctx, dreal_expr y, int rr, string name, unsigned num);
	dreal_expr dreal_mk_SHL(dreal_context ctx, dreal_expr y, int rr, string name, unsigned num);
	dreal_expr dreal_mk_INT_cmp(dreal_context ctx, dreal_expr y, dreal_expr z, Op_m pvop, string name);
	int getCMP(int rl, int rr, Op_m pvop);
	dreal_expr tran_constraint(Constraint *con, VarTable *table, int time);
	void get_constraint(vector<Constraint> consList, VarTable *table, int time, bool isTransition);
	void encode_path(CFG* ha, vector<int> patharray);

	std::vector<IndexPair> index_cache; 
	std::vector<IndexPair> core_index; 	
	void clear(){
		index_cache.clear();
		core_index.clear();
		dreal_reset(ctx);
		//dreal_del_context(ctx);
		ctx = dreal_mk_context(qf_nra);
	    dreal_set_precision(ctx, precision);
	}
public:
	Verification(){
		dreal_init();
	    ctx = dreal_mk_context(qf_nra);
		time=0;
	}
	void setPrecision(double pre){
		this->precision = pre;
	    dreal_set_precision(ctx, pre);
	}
	bool check(CFG* ha, vector<int> path);
	vector<IndexPair> get_core_index(){return core_index;}
	~Verification(){dreal_del_context(ctx);}
    void print_sol(CFG* cfg, vector<int> x);
	double getTime(){return time;}
};

class BoundedVerification{
public:
    BoundedVerification(CFG* aut,int bound,vector<int> target,double pre);
	bool check(double &time,string check);
	double getTime(){return verify.getTime();}
	~BoundedVerification(){}
private:
	CFG* cfg;
	double precision;
    bool result;
    bool reachEnd;
	int bound;
	string reachPath;
	string target_name;
	int num_of_path;
	vector<int> target;
    vector<int> path;
    vector<int> witPath;
	int stNum;
	Verification verify;
	string get_path_name(CFG *cfg,vector<int> path);
	void DFS(int intbound,int bound,int start,int end);
};




#endif

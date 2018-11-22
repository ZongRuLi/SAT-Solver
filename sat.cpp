#include<iostream>
#include "parser.h"
#include<vector>
#include "formula.h"
#include<stdlib.h>
using namespace std;

int DPLL(Formula &);
int recurseTime=0;

int main(int arg,char* argv[])
{
	srand(time(NULL));

	vector<vector<int> > clauses;
	int maxVarIndex;
	parse_DIMACS_CNF(clauses, maxVarIndex, argv[1]);

	Formula formula(clauses);
	int r = formula.init();
	if(r == unsat){
		cout<<endl<<"UNSAT"<<endl;
		return 0;
	}
//	formula.showInfo();
//	cin>>r;	
//	formula.showInfo();
//	formula.assign(1,1);

	formula.showClauses();

	int result = DPLL(formula);
	if(result == unsat)
		cout<<endl<<"UNSAT"<<endl;
	else
		cout<<endl<<"SAT"<<endl;
	cout<<"Time : "<<recurseTime<<endl;
	return 0;
}

int maxy(vector<double>);

bool showDetail = true;

int DPLL(Formula &f) 			// -1:false 0:unknown 1:true
{
	Formula::currentLevel++;
	Formula newf(f);

//	f.showClauses();

	recurseTime++;
	int result=f.checkSat();
	if(result == sat)
	{
		f.showResult();	
		Formula::currentLevel--;
		if(showDetail)cout<<"1"<<endl;
		return sat;
	}

	int x = maxy(newf.counterList);
	if(recurseTime == 1)
		x = (((int)(rand()*1200)+5)%newf.literals.size());

	int value = 0;
	if(newf.literalsPolar[x] >= 0)
		value = 1;
	else
		value = -1;

	if(showDetail)cout<<"level: "<<newf.level<<" x="<<x<<" v = "<<value<<" ";	

	Formula::conflictGraph.push_back(Node(x,value,newf.level));
	result = newf.assign(x,value);
	if(showDetail)cout<<endl;

	if(result == unsat)
	{
//		cin>>result;
		while(Formula::currentLevel == newf.level)
		{
			if(showDetail)cout<<"level: "<<newf.level<<" 3 ";
			result = newf.BCP(Formula::clauses.size()-1);
			if(showDetail)cout<<endl;
			if(result == unsat)
				return unsat;
			else if(result == sat)
				return sat;
			result = DPLL(newf);
			if(result == sat)
				return sat;
		}
		return unsat;
	}

	if(DPLL(newf)==sat)
	{
		Formula::currentLevel--;
		if(showDetail)cout<<"5"<<endl;
		return sat;
	}
	else if(Formula::currentLevel != newf.level )
	{
		cout<<"level: "<<newf.level<<" v"<<Formula::currentLevel<<endl;
		return unsat;
	}
	else 
	{	
		while(Formula::currentLevel == newf.level)
		{
			vector<int> c = Formula::clauses.back();
			for(int i=0;i<c.size();i++)
				cout<<c[i]<<": "<<newf.literals[abs(c[i])]<<" ";
			cout<<endl;

			if(showDetail)
				cout<<"level: "<<newf.level<<" 6 ";
			int result = newf.BCP(Formula::clauses.size()-1);
			if(showDetail)cout<<endl;
			if(result == sat)
				return sat;
			else if(result == unsat)
				return unsat;
			result = DPLL(newf);
			if(result == sat)
				return sat;
		}
		return unsat;
	}
}

int maxy(vector<double> c)
{
	double max=0,j=1;
	for(int i=1;i<c.size();i++)
	{
		if(max<c[i])
		{
			max = c[i];
			j = i;
		}
	}
	return j;
}








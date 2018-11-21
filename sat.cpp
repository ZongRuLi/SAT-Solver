#include<iostream>
#include "parser.h"
#include<vector>
#include "formula.h"
using namespace std;

int DPLL(Formula &);
int recurseTime=0;

int main(int arg,char* argv[])
{
	vector<vector<int> > clauses;
	int maxVarIndex;
	parse_DIMACS_CNF(clauses, maxVarIndex, argv[1]);

	Formula formula(clauses);
	formula.init();

	formula.showInfo();
//	formula.assign(1,1);

//	formula.showInfo();

	int result = DPLL(formula);
	if(result == unsat)
		cout<<endl<<"UNSAT"<<endl;
	else
		cout<<endl<<"SAT"<<endl;
	cout<<"Time : "<<recurseTime<<endl;
	return 0;
}

int maxy(vector<double>);

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
		cout<<"1"<<endl;
		return sat;
	}
	else if(result == unsat)
	{
//		cout<<"hallo"<<endl;
//		f.showInfo();
		Formula::currentLevel--;
		cout<<"level: "<<newf.level<<" 2"<<endl;
		return unsat;
	}

	int x = maxy(newf.counterList);
	int value = 0;
	if(newf.literalsPolar[x] >= 0)
		value = 1;
	else
		value = -1;

	cout<<"level: "<<newf.level<<" x="<<x<<" v = "<<value<<" ";	

	Formula::conflictGraph.push_back(Node(x,value,newf.level));
	result = newf.assign(x,value);
	cout<<endl;

	if(result == unsat)
	{
		cout<<"level: "<<newf.level<<" x="<<x<<" v = "<<-1*value<<" ";
		result = newf.assign(x,-1*value);
		cout<<endl;
		
		if(result == unsat)
		{
			Formula::currentLevel--;
			cout<<"level: "<<newf.level<<" 3"<<endl;
			return unsat;
		}
		else
		{
			result = DPLL(newf);
			Formula::currentLevel--;
			cout<<"level: "<<newf.level<<" 4"<<endl;
			return result;
		}
	}

	if(DPLL(newf)==sat)
	{
		Formula::currentLevel--;
		cout<<"5"<<endl;
		return sat;
	}
	else if(Formula::currentLevel != newf.level )
	{
		cout<<"level: "<<newf.level<<" v"<<Formula::currentLevel<<endl;
		return unsat;
	}
	else 
	{
		cout<<"level: "<<newf.level<<" x="<<x<<" v = "<<value<<" ";
		result = newf.assign(x,-1*value);
		cout<<endl;

		if(result == unsat)
		{
			Formula::currentLevel--;
			cout<<"level: "<<newf.level<<" 5.5"<<endl;
			return unsat;
		}

		result =  DPLL(newf);
		Formula::currentLevel--;
		cout<<"level: "<<newf.level<<" 6"<<endl;
		return result;
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








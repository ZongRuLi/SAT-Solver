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

//	formula.showClauses();
//	cin>>r;
	int result = DPLL(formula);
	if(result == unsat)
		cout<<endl<<"UNSAT"<<endl;
	else
		cout<<endl<<"SAT"<<endl;
//	cout<<"Time : "<<recurseTime<<endl;
	return 0;
}

int maxy(vector<double>);
void showStack(vector<Formula>);

bool showDetail = true;

int DPLL(Formula &f) 			// -1:false 0:unknown 1:true
{
	f.zero();	
	vector<Formula> fv;
	fv.push_back(new Formula(f));
	fv.back().level=Formula::currentLevel=1;
	int blevel=-1,x=0,value=0;
	while(true)
	{
		//decide next branch
		x = maxy(fv.back().counterList);
		
		value = fv.back().literalsPolar[abs(x)];
	
		if(value >=0)
			value = 1;
		else
			value = -1;

		while(true)
		{
			Formula *newf=new Formula(fv.back());	
			newf->level = Formula::currentLevel;

			Formula::conflictGraph.push_back(Node(x,value,newf->level));
			for(int i = newf->conflictGraph.size()-2;i>=0;i--)
			{
				if(newf->conflictGraph[i].literal == x)
				{
					newf->conflictGraph.pop_back();	
					break;
				}
				if(newf->conflictGraph[i].level < newf->level)
					break;
			}
	
			newf->curDec = x;newf->curValue=value;
			//cout<<newf->curDec<<",,"<<newf->curValue;
//			cout<<"//level: "<<newf->level<<" x"<<newf->curDec<<" = "<<value;
			int result = newf->assign(x,value);

			if(blevel != -1 && result != unsat)
			{
				result = newf->BCP(newf->clauses.size()-1);
				blevel=-1;
			}
			cout<<endl;

			if(result == unsat)
			{
				blevel = newf->conflictResolve(newf->conflicting);
				cout<<"Return to level "<<blevel<<endl;
				Formula::clauses.push_back(newf->conflictClause);
				int l = Formula::clauses.size();
				for(int i=0;i<Formula::conflictClause.size();i++)
				{		
					int k = Formula::conflictClause[i];
					if(k>0)
						newf->posWatched[k].push_back(l-1);
					else
						newf->negWatched[abs(k)].push_back(l-1);
				}

				newf->watchingList.push_back(pair<int,int>(newf->clauses[l-1][0],newf->clauses[l-1][1]));

				if(blevel<0)
				{
					int c;cin>>c;
					return unsat;
				}
				else
				{
					//backtracking
					while(fv.back().level != blevel)
					{
						fv.pop_back();
					}
					
					while(Formula::conflictGraph.back().level > blevel)
						Formula::conflictGraph.pop_back();

					if(blevel==0)
					{
						int c;cin>>c;
						f.conflictGraph.clear();
						Formula::currentLevel=1;
						
						fv.push_back(new Formula(f));
						
						int k=f.clauses.back()[0];
						x = abs(k);
						value = k/abs(k);
					}	
					else
					{

						x=fv.back().curDec;
						value=fv.back().curValue;
						cout<<fv.back().level<<x<<","<<value<<endl;
					
						Formula::currentLevel = blevel;
					}
				}	
			}
			else if(newf->checkSat())
			{
				newf->showResult();
				return sat;
			}
			else
			{
				Formula::currentLevel++;
				fv.push_back(new Formula((*newf)));
				break;
			}
		}
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

void showStack(vector<Formula> fs)
{
	cout<<"show stack"<<endl;
	for(int i=0;i<fs.size();i++)
	{
		cout<<fs[i].level<<" ";
		cout<<"x"<<fs[i].curDec<<"= "<<fs[i].curValue<<endl;
	}
	cout<<endl;
}






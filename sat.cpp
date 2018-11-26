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
int flag = 0;
int DPLL(Formula &f) 			// -1:false 0:unknown 1:true
{
	f.zero();	
	vector<Formula> fv;
	fv.push_back(new Formula(f));
	fv.back().level=Formula::currentLevel=1;
	int blevel=-1,x=0,value=0,antedent = -1;
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

			Formula::conflictGraph.push_back(Node(x,value,newf->level,antedent));
			antedent = -1;				

			newf->curDec = x;newf->curValue=value;
			//cout<<newf->curDec<<",,"<<newf->curValue;
			cout<<"//level: "<<newf->level<<" x"<<newf->curDec<<" = "<<value;
			int result = newf->assign(x,value);

			if(result == unsat)
			{
				blevel = newf->conflictResolve(newf->conflicting);
				cout<<"Return to level "<<blevel<<endl;

				if(blevel<0)
				{
					int c;cin>>c;
					return unsat;
				}
				else
				{
					//backtracking
					while(fv.size()>0 && fv.back().level != blevel)
					{
						fv.pop_back();
					}
					if(Formula::conflictGraph.size()>0)
					while(Formula::conflictGraph.back().level > blevel)
						Formula::conflictGraph.pop_back();
					
					
					x = newf->conflictx;
					value = newf->conflictv;
					Formula::currentLevel = blevel;

					if(newf->conflictClause.size() <= 10 || true)
					{
						newf->addClause(newf->conflictClause);
						antedent = newf->clauses.size()-1;
					}
					else
					{
						antedent = -1;
						Formula::currentLevel++;
					}				

					if(blevel == 0)
					{
						Formula *nf = new Formula(f);
						Formula::currentLevel++;
						nf->level = 1;
					
						nf->conflictGraph.push_back(Node(x,value,1,antedent));
						cout<<"//level: "<<nf->level<<" x"<<x<<" = "<<value;
						cout<<" ";
						result = nf->assign(x,value);
						cout<<endl;

						if(result == unsat)
							return unsat;

						fv.push_back(nf);
						Formula::currentLevel++;
						break;
					}
				}
			//	int e;cin>>e;	
			}
			else if(result == sat)
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






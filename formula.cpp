#include "formula.h"
#include<stdio.h>
#include<iostream>
#include<cmath>
#include<vector>
using namespace std;

int Formula::currentLevel = 0;
int Formula::initSize=0;
vector<vector<int> > Formula::posWatched;
vector<vector<int> > Formula::negWatched;
vector<vector<int> > Formula::clauses;
vector<pair<int,int> > Formula::watchingList;
vector<Formula > Formula::formulaStack;
vector<Node> Formula::conflictGraph;
vector<double> Formula::VSIDS;
vector<int> Formula::conflictClause;

int Formula::targetLevel = -1;

void showClause(vector<int>);

void Formula::zero()
{
	while(clauses.size()>initSize)
		clauses.pop_back();

	for(int i=0;i<literals.size();i++)
	{
		for(int j=0;j<posWatched[i].size();j++)
		{
			if(posWatched[i][j]>=clauses.size())
			{
				posWatched[i].erase(posWatched[i].begin()+j);
				j--;
			}
		}
		for(int j=0;j<negWatched[i].size();j++)
			if(negWatched[i][j]>=clauses.size())
			{
				negWatched[i].erase(negWatched[i].begin()+j);
				j--;
			}
	}
	conflictGraph.clear();
}

Formula::Formula()
{
}

Formula::Formula(const vector<vector<int> >& c)
{
	this->clauses = c;
}

Formula::Formula(const Formula *f)
{
	this->literals.assign(f->literals.begin(),f->literals.end());

	this->level = f->level;
//	this->conflictGraph = f.conflictGraph;
	this->counterList.assign(f->counterList.begin(),f->counterList.end());
	this->literalsPolar.assign(f->literalsPolar.begin(),f->literalsPolar.end());
//	this->resolveNum = f.resolveNum
	this->preAssign=0;
	this->curDec=f->curDec;
	this->curValue=f->curValue;
}

Formula::~Formula()
{
	
}

int Formula::init()
{
	initSize = clauses.size();

	status = unknown;
	this->currentLevel = 0;
	level = 0;
	resolveNum = 0;

	literals.push_back(-1); 		// no element named 0
	counterList.push_back(-1);
	literalsPolar.push_back(0);
	VSIDS.push_back(0);	
	posWatched.push_back(vector<int>());
	negWatched.push_back(vector<int>());


	for(int i=0;i<(int)clauses.size();i++)
	{
		clauseStatus.push_back(0);
		for(int j=0;j<(int)clauses[i].size();j++)
		{
			int k = abs(clauses[i][j]);
			// record & init all lits
			while(k >= literals.size())
			{
				literals.push_back(0);	
				
				// for counter
				counterList.push_back(0);
				literalsPolar.push_back(0);
				VSIDS.push_back(0);
				posWatched.push_back(vector<int>());
				negWatched.push_back(vector<int>());
			}
			counterList[k]++;
			if(clauses[i][j]<0)
				literalsPolar[k]--;
			else
				literalsPolar[k]++;
			
			for(int l=j-1;l>=0;l--)
			{
				if(clauses[i][j] == clauses[i][l])
				{
					clauses[i].erase(clauses[i].begin()+l);
					j--;
					break;
				}
			}
		}
	}

	// watching list init
	for(int i=0;i<(int)clauses.size();i++)
	{
		if(clauses[i].size() != 1)
		{
			int x = clauses[i][0],y = clauses[i][1];
			watchingList.push_back(pair<int,int>(x,y));
			
			if(x>0)
				posWatched[x].push_back(i);
			else if(x<0)
				negWatched[abs(x)].push_back(i);
			if(y>0)
				posWatched[y].push_back(i);
			else if(y<0)
				negWatched[abs(y)].push_back(i);
		}
		else 
		{
			int x = clauses[i][0];
			watchingList.push_back(pair<int,int>(0,x));
		
		}
	}

	//check for unit clauses
	for(int i=0;i<clauses.size();i++)
	{
		if(clauses[i].size() > 1)
			continue;
		int result = BCP(i);
		if(result == unsat)
			return unsat;
	}
	conflictGraph.clear();

	return unknown;
}

vector<int> resolve(vector<int> a,vector<int> b,int c)
{
	vector<int> x;
	int i,j;
	for(i=0;i<a.size();i++)
	{
		if(abs(a[i]) != abs(c))
			x.push_back(a[i]);
	}
	
	for(j=0;j<b.size();j++)
	{
		if(abs(b[j]) == abs(c))
			continue;
		int n=0;
		for(i=0;i<x.size();i++)
			if(b[j] == x[i])
			{
				n=1;
				break;
			}
		if(n==0)
			x.push_back(b[j]);
	}

	return x;
}

void showClause(vector<int> c)
{
	cout<<endl;
	for(int i=0;i<c.size();i++)
		cout<<c[i]<<" ";
	cout<<endl;
}

int Formula::conflictResolve(int conflicting)
{
//	showInfo();
//	if(this->level==8)
	{
		for(int j=0;j<conflictGraph.size();j++)
		{
			Node n = conflictGraph[j];
			printf("x%02d=%2d@%02d ",n.literal,n.value,n.level);
		}
		cout<<endl;
	}

	//First UIP
	vector<int> clause;
        clause.assign(clauses[conflicting].begin(),clauses[conflicting].end());

        int x=-1;//cout<<"FirstUIP"<<endl;
        while(checkUIP(clause,&x))
        {	
//`		if(this->level==12)
		{
			showClause(clause);
			cout<<"+";
			showClause(clauses[conflictGraph[x].antecedent]);
		}
                clause = resolve(clause,clauses[conflictGraph[x].antecedent],conflictGraph[x].literal);
		conflictGraph.erase(conflictGraph.begin()+x);
                int x=-1;
        }

//		cout<<"Done FirstUIP"<<endl;
	conflictClause = clause;
	cout<<"conflict clause:"<<endl;
	showClause(conflictClause);

	
	int maxLevel=-1;
	for(int i=0;i<clause.size();i++)
	{
		int k=abs(clause[i]);
		for(int j=conflictGraph.size()-1;j>=0;j--)
		{
			if(conflictGraph[j].level == this->level && k == conflictGraph[j].literal)
			{
				this->conflictx = conflictGraph[j].literal;
				this->conflictv = conflictGraph[j].value*-1;
			}
			else if(k==conflictGraph[j].literal)
			{
				if(this->level == 12)
					cout<<"k "<<k<<"@"<<conflictGraph[j].level<<" ";

				if(maxLevel < conflictGraph[j].level)
					maxLevel = conflictGraph[j].level;
			}
		}
	}	
	if(maxLevel==-1 && clause.size() == 1)
		maxLevel=0;
	cout<<"this level is "<<this->level<<endl;
	return maxLevel; 
}

void Formula::addClause(vector<int> c)
{
	clauses.push_back(c);
	int l = clauses.size();

	int k=0;
	for(int i=0;i<c.size();i++)
	{
		int m = c[i];
		if(m>0)
		{
			int k=0;
			for(int j=0;j<posWatched[m].size();j++)
			{
				if(l-1 == posWatched[m][j])
				{
					k=1;
					break;
				}
			}
			if(k == 0)
				posWatched[m].push_back(l-1);
		}
		else if(m<0)
		{
			m = abs(m);
			int k=0;
			for(int j=0;j<negWatched[m].size();j++)
			{
				if(l-1 == negWatched[m][j])
				{
					k=1;
					break;
				}
			}
			if(k == 0)
				negWatched[m].push_back(l-1);
		}
	}
	int p=conflictClause[0],q;
	if(conflictClause.size() > 1)
		q = conflictClause[1];
	else	
		q = 0;

	watchingList.push_back(pair<int,int>(p,q));
}

bool Formula::checkUIP(vector<int> c,int *x)
{
	int n=0,ijk=0;
        *x=-1;
        for(int i=0;i<c.size();i++)
        {
                int k=abs(c[i]);
                for(int j = conflictGraph.size()-1;j>=0;j--)
                {
			
                        if(conflictGraph[j].level!=this->level)
                                break;
                        //if(conflictGraph[j].antecedent<0)
                          //      continue;
                        if(k == (int)conflictGraph[j].literal)
                        {
                                n++;
                                if(*x<j)
                                {
                                	*x=j;
//                                	cout<<"x ="<<*x<<endl;
				}      
                                break;
                        }
                }
        }
	if(n>=2)
		return true;
        if(n==1)
                return false;
        cout<<endl<<"Warning!! x= "<<*x<<endl;
        return false;
}


int Formula::BCP(int c)
{
	cout<<" BCP clause "<<c<<" in "<<this->level<<" ";
	showClause(clauses[c]);
        for(int i=0;i<clauses[c].size();i++)
        	cout<<literals[abs(clauses[c][i])]<<" ";
	cout<<endl;

	int result = unknown,n=0,value=0,x=0;
	for(int i=0;i<clauses[c].size();i++)
	{
		int j = clauses[c][i];
		if(literals[abs(j)] == 0)
			n++;
	}
	if(n>=2)
	{
		cout<<"Something got wrong"<<endl;
		int c;cin>>c;
		
	}
	if(n==0)
		return unknown;
	
	for(int i=0;i<clauses[c].size();i++)
	{
		int j = clauses[c][i];
		if(literals[abs(j)] == 0)
		{
			x = j;
			value = abs(x)/x;
			conflictGraph.push_back(Node(abs(x),value,this->level,c));
			result = assign(abs(x),value);
			n++;
		}
	}
	
	return result;
}

int Formula::updateWatchingList(int c,int x)
{
	int otherWatcher=0;
	if(x == abs(watchingList[c].first))
		otherWatcher = watchingList[c].second;
	else
		otherWatcher = watchingList[c].first;

	int l=0;
	for(int i=0;i<clauses[c].size();i++)
	{
		int j = clauses[c][i];
		if(literals[abs(j)]*j >= 0 && j!=otherWatcher && abs(j)!=x)
			l = j;
	}

	// case 1
	if(l!=0)
	{
		if(l>0)
			posWatched[l].push_back(c);
		else
			negWatched[abs(l)].push_back(c);

		watchingList[c].first = otherWatcher;
		watchingList[c].second = l;
		
//		cout<<"Change "<<x<<" to "<<l<<" on "<<c<<endl;	
		
		return -100;
	}	

	if(literals[abs(otherWatcher)] == 0)
	{
		// do BCP
		return BCP(c);
		
	}

	if(literals[abs(otherWatcher)] == otherWatcher/abs(otherWatcher))
	{
		//resolve
		return checkSat();
	}
	else
	{
		//conflict
		cout << " !!conflict!! in "<<c<<": ";
		showClause(clauses[c]);
		for(int i=0;i<clauses[c].size();i++)
			cout<<literals[abs(clauses[c][i])]<<" ";
		cout<<endl;

		cout<<"Watcher: "<<x<<","<<otherWatcher<<endl;

		conflicting = c;
		return unsat;
	}
}

int Formula::assign(int x,int value) 	//-1:false
{					// 0:unknown
	literals[x] = value;		// 1:true`

	counterList[x] = -1;		// will never show up

	int result = unknown;

	if(value > 0)
	{
		for(int i=0;i<negWatched[x].size();i++)
		{
			result = updateWatchingList(negWatched[x][i],x);
			if(result == -100)
			{
				negWatched[x].erase(negWatched[x].begin()+i);
				i--;
			}
			if(result == -1000)
				return unknown;
			if(result == unsat)
			{
		//		literals[x] = 0;
				return unsat;	
			}
			if(result == sat)
				return sat;			
		}
	}
	else if(value < 0)
	{
		for(int i=0;i<posWatched[x].size();i++)
		{
			result = updateWatchingList(posWatched[x][i],x);
			if(result == -100)
			{
				posWatched[x].erase(posWatched[x].begin()+i);
				i--;
			}
			if(result == -1000)
				return unknown;
			if(result == unsat)
			{
//				literals[x] = 0;
				return unsat;
			}
			if(result == sat)
				return sat;
		}
	}
//	showInfo();
	return unknown;
}

int Formula::checkSat()
{
	int n=0;
	for(int i=0;i<clauses.size();i++)
	{
		int resolve = 0;
		
		for(int j=0;j<clauses[i].size();j++)
		{
			int k=clauses[i][j];
			if(k*literals[abs(k)]>0)
			{
				resolve=1;
				break;
			}
		}
		if(resolve!=1)
			return unknown;
	}
	return sat;
}
	
void Formula::firstUIP()
{
}

void Formula::showClauses()
{
	for(int i=0;i<(int)clauses.size();i++)
	{
		cout<<i<<" |  ";
		for(int j=0;j<(int)clauses[i].size();j++)
		{
			cout<<clauses[i][j]<<" ";
		}
		cout<<"\t\t"<<watchingList[i].first<<" ";
		cout<<watchingList[i].second<<endl;
	}
}

void Formula::showInfo()
{
	cout<<endl<<"clauses"<<endl;
	this->showClauses();

	int l=literals.size();
	cout<<endl<<"literals"<<"\t\t\tpos/neg"<<endl;
	
	for(int ij=1;ij<l;ij++)
	{
		cout<<ij<<": ";cout<<this->literals[ij]<<"\t";
		cout<<this->counterList[ij]<<"\t";
		cout<<literalsPolar[ij]<<"\t";
		for(int j=0;j<(int)posWatched[ij].size();j++)
			cout<<posWatched[ij][j]<<" ";
		cout<<"/";
		for(int j=0;j<(int)negWatched[ij].size();j++)
			cout<<negWatched[ij][j]<<" ";
		cout<<endl;
	}
	cout<<"end"<<endl;
}

void Formula::showResult()
{
	cout<<endl<<"SAT"<<endl;
	for(int i=1;i<(int)literals.size();i++)
	{
		cout<<i<<": "<<literals[i]<<endl;
	}
	cout<<endl;
}

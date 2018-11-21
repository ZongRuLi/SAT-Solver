#include "formula.h"
#include<iostream>
#include<cmath>
#include<vector>
using namespace std;

int Formula::currentLevel = 0;
vector<vector<int> > Formula::posWatched;
vector<vector<int> > Formula::negWatched;
vector<vector<int> > Formula::clauses;
vector<pair<int,int> > Formula::watchingList;
vector<Formula > Formula::formulaStack;
vector<Node> Formula::conflictGraph;
vector<double> Formula::VSIDS;
vector<int> Formula::conflictClause;

Formula::Formula()
{
}

Formula::Formula(const vector<vector<int> >& c)
{
	this->clauses = c;
}

Formula::Formula(const Formula &f)
{
	this->literals.assign(f.literals.begin(),f.literals.end());

	this->level = Formula::currentLevel;
//	this->conflictGraph = f.conflictGraph;
	this->counterList.assign(f.counterList.begin(),f.counterList.end());
	this->literalsPolar.assign(f.literalsPolar.begin(),f.literalsPolar.end());
//	this->resolveNum = f.resolveNum
	this->preAssign=0;
}

Formula::~Formula()
{
	
}

int Formula::init()
{
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
			if(x>0)
				posWatched[x].push_back(i);
			else if(x<0)
				negWatched[abs(x)].push_back(i);
		}
	}

	//check for unit clauses
/*	for(int i=0;i<clauses.size();i++)
	{
		if(clauses[i].size() > 1)
			continue;
		int result = BCP(i);
		if(result == unsat)
			return unsat;
	}
*/
	return unknown;
}

void Formula::conflictResolve(int conflicting)
{
	cout<<"conflict resolve at level "<<currentLevel<<endl;
}


int Formula::BCP(int c)
{
//	cout<<" BCP clause "<<c<<" ";
	int result = unknown,n=0,value=0,x=0;
	for(int i=0;i<clauses[c].size();i++)
	{
		int j = clauses[c][i];
		if(literals[abs(j)] == 0)
		{
			x = j;
			value = abs(x)/x;
	//		conflictGraph.push_back(Node(abs(x),value,this->level,c));
			result = assign(abs(x),value);
		}
	}
	return result;
}

int Formula::updateWatchingList(int c,int x)
{
	if(clauses[c].size() == 1)
		return unsat;

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
		return unknown;
	}
	else
	{
		//conflict
//		cout << " !!conflict!! in "<<c<<" ";
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
			if(result == unsat)
			{
				literals[x] = 0;
				return unsat;	
			}			
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
			if(result == unsat)
			{
				literals[x] = 0;
				return unsat;
			}
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
		
		int lit1 = watchingList[i].first;
		int lit2 = watchingList[i].second;

		if(lit1*literals[abs(lit1)]>0)
			resolve = 1;
		if(lit2*literals[abs(lit2)]>0)
			resolve = 1;

		if(resolve == 0)
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

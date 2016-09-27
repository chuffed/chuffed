#include <ctime>
#include <cstring>
#include <iostream>
#include <stdint.h>
#include <errno.h>

#include <utility>

#include <chuffed/core/engine.h>
#include <chuffed/core/propagator.h>
#include <chuffed/branching/branching.h>
#include <chuffed/globals/mddglobals.h>

// Nonograms
static void nonogram(vec<IntVar*>& x, vec<int>& blocks);

static void nonogramDFA(vec<int>& blocks,
                vec< vec<int> >& output);

static void skipComments(std::istream& i)
{
   assert( i.peek() == '#' || i.peek() == '\n' );
   
   while( i.peek() != '\n' && i.peek() != EOF )
      i.ignore();
   
   i.ignore();
}

class Nonogram : public Problem {
public:
    int r;
    int c;

    vec<IntVar*> x;

    Nonogram() {
        // Generate instance
        
        while(std::cin.peek() == '#' || std::cin.peek() == '\n')
            skipComments(std::cin);

        std::cin >> r;
        std::cin >> c;
        
//        std::cout << r << " " << c << std::endl;
         
        for (int i = 0; i < r*c; i++) {
            x.push(newIntVar(0, 2));
            x.last()->specialiseToEL();
        }

        int n;
        for( int j = 0; j < r; j++ )
        {
            vec<int> row;
            vec<IntVar*> rowvars;
            
            for( int kk = 0; kk < c; kk++ )
            {
                rowvars.push( x[j*c + kk] );
            }

            std::cin >> n;
            while( n != 0 )
            {
                row.push(n);
                std::cin >> n;
            }

            nonogram(rowvars, row);
        }

        for( int j = 0; j < c; j++ )
        {
            vec<int> col;
            vec<IntVar*> colvars;

            for( int kk = 0; kk < r; kk++ )
            {
                colvars.push( x[kk*c + j] );
            }

            std::cin >> n;
            while( n != 0 )
            {
                col.push(n);
                std::cin >> n;
            }

            nonogram(colvars,col);
        }
        

        vec<IntVar*> pref_order;
        for (int i = 0; i < x.size(); i++ ) {
            pref_order.push(x[i]);
        }

        output_vars(pref_order);
        branch(pref_order, VAR_INORDER, VAL_MIN);
    }
 
    void print(std::ostream& os) {
      for (int i = 0; i < x.size(); i++) {
        int v = x[i]->getVal();
        os << i << ": " << v << "\n";
      }
    }
   
};

static void nonogram(vec<IntVar*>& x, vec<int>& blocks)
{
    vec< vec<int> > dfa;
    vec< int > accepts;
    nonogramDFA(blocks,dfa);
    accepts.push(dfa.size());

    if( so.mdd )
    {
//        mdd_regular(x, dfa.size()+1, 2, dfa, 1, accepts);
        MDDOpts mopts;
        mdd_regular(x, dfa.size(), 2, dfa, 1, accepts, true, mopts);
    } else {
//        regular(x, dfa.size()+1, 2, dfa, 1, accepts);
        regular(x, dfa.size(), 2, dfa, 1, accepts);
    }
}

// Need to fix DFA format.
static void nonogramDFA(vec<int>& blocks,
                vec< vec<int> >& output)
{
    output.clear();
    
    // All zeros
    if( blocks.size() < 1 )
    {
        output.push();
        output.last().push(1);
        output.last().push(0);
        return;
    }
    
    output.push();
    output.last().push(1);
    output.last().push(2);
    
    for( int i = 0; i < blocks.size() - 1; i++ )
    {
        for( int j = 1; j < blocks[i]; j++ )
        {
            output.push();
            output.last().push(0);
            output.last().push(output.size()+1);
        }
        
        output.push();
        output.last().push(output.size()+1);
        output.last().push(0);
        
        output.push();
        output.last().push(output.size());
        output.last().push(output.size()+1);
    }

    for( int j = 1; j < blocks[blocks.size()-1]; j++ )
    {
        output.push();
        output.last().push(0);
        output.last().push(output.size()+1);
    }
    output.push();
    output.last().push(output.size());
    output.last().push(0);
}

int main(int argc, char** argv) {
    parseOptions(argc, argv);

    engine.solve(new Nonogram());

    return 0;
}

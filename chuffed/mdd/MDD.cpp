#include <iostream>

#ifdef __APPLE__
#include <memory>
#define MEMCPY std::memcpy
#else
#include <cstring>
#define MEMCPY memcpy
#endif

#include <cassert>
#include <climits>
#include <iostream>
#include <chuffed/mdd/MDD.h>

#define OPCACHE_SZ 100000
#define CACHE_SZ 180000

static MDDEdge mkedge(unsigned int val, unsigned int dest)
{
   MDDEdge edge = {
      (int) val,
      dest
   };
   return edge;
}

MDDNode MDDTable::allocNode(int n_edges)
{
   return ( (MDDNodeEl*) malloc(sizeof(MDDNodeEl) + (n_edges - 1)*sizeof(MDDEdge)) );
}

inline void MDDTable::deallocNode(MDDNode node)
//void MDDTable::deallocNode(MDDNode node)
{
   free(node);
}

MDDTable::MDDTable(int _nvars)
   : nvars( _nvars ),
     opcache( OpCache(OPCACHE_SZ) ),
#ifdef SPLIT_CACHE
      cache(new NodeCache[nvars]),
#else
//      cache(CACHE_SZ),
      cache(),
#endif
      stack(),
      intermed_maxsz(2),
      nodes()
{
   // Initialize \ttt and \fff.
   nodes.push_back(NULL); // false node
   nodes.push_back(NULL); // true node
   status.push_back(0);
   status.push_back(0);

   intermed = allocNode(intermed_maxsz);
}

MDDTable::~MDDTable(void)
{
   deallocNode(intermed);
   for( unsigned int i = 2; i < nodes.size(); i++ )
      deallocNode(nodes[i]);

#ifdef SPLIT_CACHE
   delete [] cache;
#endif
}

// Insert a node with edges
// stack[start,...].
_MDD MDDTable::insert(unsigned int var, unsigned int low, unsigned int start, bool expand)
{
#ifdef SPLIT_CACHE
//   NodeCache& varcache( cache[node[0]] );
   NodeCache& varcache( cache[(*node)[0]] );
#else
   NodeCache& varcache( cache );
#endif
   
   // Ensure there's adequate space in the intermed node.
   if( intermed_maxsz < (stack.size() - start) )
   {
      while( intermed_maxsz < (stack.size() - start) )
         intermed_maxsz *= 2;

      deallocNode(intermed);
      intermed = allocNode(intermed_maxsz);
   }

   // Collapse joined edges and shift to the intermediate node.
   unsigned int jj = 0;
   unsigned int ii = start;

   while(ii < stack.size() && stack[ii].dest == low)
   {
     ii++;
   }
   if(ii < stack.size())
     intermed->edges[jj++] = stack[ii];
   for( ; ii < stack.size(); ii++ )
   {
      if( stack[ii].dest != intermed->edges[jj-1].dest )
      {
         intermed->edges[jj] = stack[ii];
         jj++;
      }
   }

   if( jj == 0 && !expand )
   {
      // Constant node.
      unsigned int ret = stack[start].dest;
      stack.resize(start);
      return ret;
   }
   // Fill in the rest of intermed, and search in the cache.
   intermed->var = var;
   intermed->low = low;
   intermed->sz = jj;

   NodeCache::iterator res = varcache.find(intermed);

   if( res != varcache.end() )
   {
      stack.resize(start);
      return (*res).second;
   }

   MDDNode act = allocNode(intermed->sz);

   MEMCPY(act,intermed,sizeof(MDDNodeEl) + (((int)intermed->sz) - 1)*(sizeof(MDDEdge)));

   varcache[act] = nodes.size();
   nodes.push_back(act);
   status.push_back(0);
   
   stack.resize(start); // Remove the current node from the stack.
   return nodes.size() - 1;
}

template <class T>
_MDD MDDTable::tuple(vec<T>& tpl)
{
   _MDD res = MDDTRUE;
   
   unsigned int start = stack.size();
   for( int i = tpl.size() - 1; i >= 0; i-- )
   {
      stack.push_back( mkedge(tpl[i],res) );
      stack.push_back( mkedge(tpl[i]+1,MDDFALSE) );
      res = insert(i, MDDFALSE, start);
   }
   
   return res;
}

template _MDD MDDTable::tuple(vec<int>& tpl);

_MDD MDDTable::mdd_vareq(int var, int val)
{
   assert( var < nvars );
   
   unsigned int start = stack.size();
   
   stack.push_back( mkedge(val,MDDTRUE) );
   stack.push_back( mkedge(val+1,MDDFALSE) );

   _MDD res = insert(var, MDDFALSE, start);
   assert( stack.size() == start );
      
   return res;
}

_MDD MDDTable::mdd_varlt(int var, int val)
{
   unsigned int start = stack.size();
   
   stack.push_back( mkedge(val, MDDFALSE) );
   _MDD res = insert(var, MDDTRUE, start);

   assert(stack.size() == start);

   return res;
}

_MDD MDDTable::mdd_vargt(int var, int val)
{
   unsigned int start = stack.size();
   stack.push_back( mkedge(val+1, MDDTRUE) );

   _MDD res = insert(var, MDDFALSE, start);
   assert(stack.size() == start);
   
   return res;      
}


_MDD MDDTable::mdd_case(int var, std::vector<edgepair>& cases)
{
   if( cases.size() == 0 )
      return MDDFALSE;

   _MDD res = MDDFALSE;

   for( unsigned int ii = 0; ii < cases.size(); ii++ )
   {
       res = mdd_or(res,
                mdd_and(mdd_vareq(var,cases[ii].first),cases[ii].second));
   }
   return res;
}

// FIXME: Completely bogus.
_MDD MDDTable::bound(_MDD root, vec< intpair >& range)
{
  return root;
  /*
   if( root == MDDFALSE || root == MDDTRUE )
      return root; 
   
   assert( ((int) nodes[root]->var) < range.size() );

   unsigned int var = nodes[root]->var;
   int lb = range[var].first;
   int ub = range[var].second;

   unsigned int start = stack.size();

   unsigned int prev = nodes[root]->low;
   unsigned int ii = 0;
   while( ii < nodes[root]->sz && nodes[root]->edges[ii].val < lb )
   {
      prev = nodes[root]->edges[ii].dest; 
      ii++;
   }
   
   // Eliminate node if a single edge spans the whole range.
   if( nodes[root]->edges[ii].val > ub )
   {
      return prev;
   }
   if( nodes[root]->edges[ii].val == lb && 
        (nodes[root]->sz == ii+1 || nodes[root]->edges[ii+1].val > ub) )
   {
      return nodes[root]->edges[ii].dest;
   }

   if( nodes[root]->edges[ii].val > lb )
      stack.push_back( mkedge(lb, prev) );
   
   for( ; ii < nodes[root]->sz && nodes[root]->edges[ii].val <= ub; ii++ )
   {
      stack.push_back( nodes[root]->edges[ii] ); 
   }
   stack.push_back( mkedge(ub+1,MDDFALSE) );
   
   _MDD res = insert(var, MDDFALSE, start);
   return res;
   */
}

_MDD MDDTable::expand(int var, _MDD r)
{
   if( r == MDDFALSE )
      return MDDFALSE;
   
   _MDD res = opcache.check(OP_EXPAND, var, r);
   if( res != UINT_MAX )
       return res;

   int cvar = (r == MDDTRUE) ? nvars : nodes[r]->var;
   assert( cvar >= var && var <= nvars );
   
   int start = stack.size();
   int low;

   if( cvar == var )
   {
      if( r == MDDTRUE )
          return r;

      low = expand(var+1, nodes[r]->low);
      for( unsigned int ii = 0; ii < nodes[r]->sz; ii++ )
      {
         stack.push_back(
            mkedge(nodes[r]->edges[ii].val,
                   expand(var+1, nodes[r]->edges[ii].dest))
          );
      }
   } else {
      // var < cvar
      assert( var < cvar );
      low = expand(var+1, r);
   }
   res = insert(var, low, start, true); // Make sure it doesn't collapse the nodes.
   assert(nodes[res]->var == (unsigned int) var);

   opcache.insert(OP_EXPAND,var,r,res);

   return res;
}

_MDD MDDTable::mdd_and(_MDD a, _MDD b)
{
   if( a == MDDFALSE || b == MDDFALSE )
      return MDDFALSE;
   if( a == MDDTRUE )
      return b;
   if( b == MDDTRUE )
      return a;

   _MDD res = a < b ? opcache.check(OP_AND,a,b)
                   : opcache.check(OP_AND,b,a);
   if( res != UINT_MAX )
       return res;
   
   unsigned int start = stack.size();
   unsigned int var; 
   unsigned int low;
   if( nodes[a]->var < nodes[b]->var )
   {
      var = nodes[a]->var;
      low = mdd_and(nodes[a]->low, b);
      for( unsigned int ii = 0; ii < nodes[a]->sz; ii++ )
      {
         stack.push_back(
            mkedge(nodes[a]->edges[ii].val,
                   mdd_and(nodes[a]->edges[ii].dest, b))
          );
      }
   } else if( nodes[a]->var > nodes[b]->var ) {
      var = nodes[b]->var;
      low = mdd_and(a,nodes[b]->low);
      for( unsigned int ii = 0; ii < nodes[b]->sz; ii++ )
      {
         stack.push_back(
            mkedge(nodes[b]->edges[ii].val,
                   mdd_and(a, nodes[b]->edges[ii].dest))
          );
      }
   } else {
      // nodes[a]->var == nodes[b]->var
      var = nodes[a]->var;
      low = mdd_and(nodes[a]->low, nodes[b]->low);
      
      _MDD aprev = nodes[a]->low;
      _MDD bprev = nodes[b]->low;

      // Say we have:
      // A: (0: a1), (2: a2), (3: a3)
      // B: (0: b1), (1: b2), (3: b3), (7: b4)
      // A /\ B will be: (0: a1 /\ b1), (1: a1 /\ b2), (2: a2 /\ b2), (3: a3 /\ b3), (7: a3 /\ b4).
      // When unequal, we want to conjoin the least one with the *previous* value from the previous
      // pair.
      unsigned int ii = 0;
      unsigned int jj = 0;
      while( ii < nodes[a]->sz && jj < nodes[b]->sz )
      {
         if( nodes[a]->edges[ii].val < nodes[b]->edges[jj].val )
         {
            aprev = nodes[a]->edges[ii].dest;
            stack.push_back( mkedge(nodes[a]->edges[ii].val, mdd_and(aprev, bprev)) );
            ii++;
         } else if( nodes[a]->edges[ii].val > nodes[b]->edges[jj].val ) {
            bprev = nodes[b]->edges[jj].dest;
            stack.push_back( mkedge(nodes[b]->edges[jj].val, mdd_and(aprev, bprev)) );
            jj++;
         } else {
            // a_val == b_val
            aprev = nodes[a]->edges[ii].dest;
            bprev = nodes[b]->edges[jj].dest;
            stack.push_back( mkedge(nodes[a]->edges[ii].val, mdd_and(aprev, bprev)) );
            ii++;
            jj++; 
         }
      }
      while( ii < nodes[a]->sz )
      {
         aprev = nodes[a]->edges[ii].dest;
         stack.push_back( mkedge(nodes[a]->edges[ii].val, mdd_and(aprev, bprev)) );
         ii++;
      }
      while( jj < nodes[b]->sz )
      {
         bprev = nodes[b]->edges[jj].dest;
         stack.push_back( mkedge(nodes[b]->edges[jj].val, mdd_and(aprev, bprev)) );
         jj++;
      }
   }

   res = insert(var, low, start);
   if( a < b )
       opcache.insert(OP_AND,a,b,res);
   else
       opcache.insert(OP_AND,b,a,res);

   return res;
}

// Should abstract out to mdd_apply(op, a, b).
_MDD MDDTable::mdd_or(_MDD a, _MDD b)
{
   if( a == MDDTRUE || b == MDDTRUE )
      return MDDTRUE;
   if( a == MDDFALSE )
      return b;
   if( b == MDDFALSE )
      return a;

   _MDD res = a < b ? opcache.check(OP_OR,a,b)
                   : opcache.check(OP_OR,b,a);
   if( res != UINT_MAX )
       return res;
   
   unsigned int start = stack.size();
   unsigned int var; 
   unsigned int low;
   if( nodes[a]->var < nodes[b]->var )
   {
      var = nodes[a]->var;
      low = mdd_or(nodes[a]->low, b);
      for( unsigned int ii = 0; ii < nodes[a]->sz; ii++ )
      {
         stack.push_back(
            mkedge(nodes[a]->edges[ii].val,
                   mdd_or(nodes[a]->edges[ii].dest, b))
          );
      }
   } else if( nodes[a]->var > nodes[b]->var ) {
      var = nodes[b]->var;
      low = mdd_or(a, nodes[b]->low);
      for( unsigned int ii = 0; ii < nodes[b]->sz; ii++ )
      {
         stack.push_back(
            mkedge(nodes[b]->edges[ii].val,
                   mdd_or(a, nodes[b]->edges[ii].dest))
          );
      }
   } else {
      // nodes[a]->var == nodes[b]->var
      var = nodes[a]->var;
      low = mdd_or(nodes[a]->low, nodes[b]->low);
      
      _MDD aprev = nodes[a]->low;
      _MDD bprev = nodes[b]->low;

      // Say we have:
      // A: (0: a1), (2: a2), (3: a3)
      // B: (0: b1), (1: b2), (3: b3), (7: b4)
      // A /\ B will be: (0: a1 /\ b1), (1: a1 /\ b2), (2: a2 /\ b2), (3: a3 /\ b3), (7: a3 /\ b4).
      // When unequal, we want to conjoin the least one with the *previous* value from the previous
      // pair.
      unsigned int ii = 0;
      unsigned int jj = 0;
      while( ii < nodes[a]->sz && jj < nodes[b]->sz )
      {
         if( nodes[a]->edges[ii].val < nodes[b]->edges[jj].val )
         {
            aprev = nodes[a]->edges[ii].dest;
            stack.push_back( mkedge(nodes[a]->edges[ii].val, mdd_or(aprev, bprev)) );
            ii++;
         } else if( nodes[a]->edges[ii].val > nodes[b]->edges[jj].val ) {
            bprev = nodes[b]->edges[jj].dest;
            stack.push_back( mkedge(nodes[b]->edges[jj].val, mdd_or(aprev, bprev)) );
            jj++;
         } else {
            // a_val == b_val
            aprev = nodes[a]->edges[ii].dest;
            bprev = nodes[b]->edges[jj].dest;
            stack.push_back( mkedge(nodes[a]->edges[ii].val, mdd_or(aprev, bprev)) );
            ii++;
            jj++; 
         }
      }
      while( ii < nodes[a]->sz )
      {
         aprev = nodes[a]->edges[ii].dest;
         stack.push_back( mkedge(nodes[a]->edges[ii].val, mdd_or(aprev, bprev)) );
         ii++;
      }
      while( jj < nodes[b]->sz )
      {
         bprev = nodes[b]->edges[jj].dest;
         stack.push_back( mkedge(nodes[b]->edges[jj].val, mdd_or(aprev, bprev)) );
         jj++;
      }
   }

   res = insert(var, low, start);
   if( a < b )
       opcache.insert(OP_OR,a,b,res);
   else
       opcache.insert(OP_OR,b,a,res);

   return res;
}

_MDD MDDTable::mdd_exist(_MDD root, unsigned int var)
{
   if( root == MDDTRUE || root == MDDFALSE )
       return root;

   unsigned int r_var = nodes[root]->var;
   if( r_var > var )
       return root;
   
   _MDD res;
   if( (res = opcache.check(OP_EXIST,root,var)) != UINT_MAX )
       return res;
   
   if( r_var == var )
   {
      _MDD res = MDDFALSE;
      for( unsigned ii = 0; ii < nodes[root]->sz; ii++ )
      {
         res = mdd_or( res, nodes[root]->edges[ii].dest );
      }
      opcache.insert(OP_EXIST,root,var,res);
      return res;
   }

   // r_var < var
   unsigned int start = stack.size();
   unsigned int low = mdd_exist(nodes[root]->low, var);
   for( unsigned int ii = 0; ii < nodes[root]->sz; ii++ )
   {
      stack.push_back( mkedge( nodes[root]->edges[ii].val,
                               mdd_exist(nodes[root]->edges[ii].dest, var) ) );
   }
   res = insert(r_var, low, start);
   opcache.insert(OP_EXIST,root,var,res);
   return res;
}

_MDD MDDTable::mdd_not(_MDD root)
{
   if( root == MDDTRUE )
      return MDDFALSE; 
   if( root == MDDFALSE )
      return MDDTRUE; // Will need to handle long edges.
   
   unsigned int var = nodes[root]->var;
   unsigned int start = stack.size();
   
   unsigned int low = mdd_not(nodes[root]->low);
    
   for( unsigned int ii = 0; ii < nodes[root]->sz; ii++ )
   {
      stack.push_back( mkedge( nodes[root]->edges[ii].val,
                               mdd_not(nodes[root]->edges[ii].dest) ) );
   }
   _MDD res = insert(var, low, start);
   return res;
}

bool MDDTable::mdd_leq(_MDD a, _MDD b)
{
  if(a == MDDFALSE)
    return true;
  if(b == MDDTRUE)
    return true;

  if(a == MDDTRUE)
    return false; // b != MDDTRUE
  if(b == MDDFALSE)
    return false; // a != MDDFALSE

   unsigned int res = opcache.check(OP_LEQ,a,b);
   if(res != UINT_MAX)
       return res;
   
   assert(nodes[a]->var == nodes[b]->var);

   res = true;

   unsigned int ii = 0;
   unsigned int jj = 0;
   _MDD aprev = nodes[a]->low;
   _MDD bprev = nodes[b]->low;
   while(ii < nodes[a]->sz && jj < nodes[b]->sz)
   {
      if(!mdd_leq(aprev, bprev))
      {
         res = false;
         goto _mdd_leq_done;
      }
      int aval = nodes[a]->edges[ii].val;
      int bval = nodes[b]->edges[jj].val;
      
      if(aval <= bval)
      {
         aprev = nodes[a]->edges[ii].dest;
         ii++; 
      }
      if(bval <= aval)
      {
         bprev = nodes[b]->edges[jj].dest;
         jj++;
      }
   }
   while(ii < nodes[a]->sz)
   {
      if(!mdd_leq(aprev, bprev))
      {
         res = false;
         goto _mdd_leq_done;
      }
      aprev = nodes[a]->edges[ii].dest;
      ii++;
   }
   while(jj < nodes[b]->sz)
   {
      if(!mdd_leq(aprev, bprev))
      {
         res = false;
         goto _mdd_leq_done;
      }
      bprev = nodes[b]->edges[jj].dest;
      jj++;
   }
   // Last pair
   res = mdd_leq(aprev, bprev);

_mdd_leq_done:
   opcache.insert(OP_LEQ,a,b,res);
   return res;
}

void MDDTable::clear_status(_MDD r)
{
    if( !status[r] )
        return;
    status[r] = 0;

    if( r == MDDFALSE || r == MDDTRUE )
        return;

    clear_status(nodes[r]->low);
    for( unsigned int ii = 0; ii < nodes[r]->sz; ii++ )
        clear_status(nodes[r]->edges[ii].dest);
}

void MDDTable::print_nodes(void)
{
#if 1
   for( unsigned int i = 2; i < nodes.size(); i++ )
   {
      print_node(i);
   }
#else
   std::cout << nodes.size() << std::endl;
#endif
}

void MDDTable::print_node(_MDD r)
{
   std::cout << r << "(" << nodes[r]->var << "): ";
   std::cout << "(..," << nodes[r]->low << ")"; 
   for(unsigned int jj = 0; jj < nodes[r]->sz; jj ++)
       std::cout << " (" << nodes[r]->edges[jj].val << "," << nodes[r]->edges[jj].dest << ")";
   std::cout << std::endl;
}

void MDDTable::print_mdd(_MDD r)
{
   std::vector<_MDD> queued;
   queued.push_back(r);
   status[0] = 1;
   status[1] = 1;
   status[r] = 1;
   unsigned int head = 0;

   while( head < queued.size() )
   {
      _MDD n = queued[head];

      print_node(n);
      for( unsigned int jj = 0; jj < nodes[n]->sz; jj++ )
      {
         if( status[nodes[n]->edges[jj].dest] == 0 )
         {
            status[nodes[n]->edges[jj].dest] = 1;
            queued.push_back(nodes[n]->edges[jj].dest);
         }
      }
      head++;
   }
   for( unsigned int i = 0; i < queued.size(); i++ )
   {
       status[queued[i]] = 0;
   }
   status[0] = 0;
   status[1] = 0;
}

void MDDTable::print_mdd_tikz(_MDD r)
{
   assert( 0 );
   return;
#if 0
   std::cout << "\\documentclass{article}\n";

   std::cout << "\\usepackage{tikz}\n";
   std::cout << "\\usetikzlibrary{arrows,shapes}\n";
   std::cout << "\\begin{document}\n";
   std::cout << "\\begin{tikzpicture}\n";
   std::cout << "\\tikzstyle{vertex}=[draw,circle,fill=black!25,minimum size=20pt,inner sep=0pt]\n";
   std::cout << "\\tikzstyle{smallvert}=[circle,fill=black!25,minimum size=5pt,inner sep=0pt]\n";
   std::cout << "\\tikzstyle{edge} = [draw,thick,->]\n";
   std::cout << "\\tikzstyle{kdedge} = [draw,thick,=>,color=red]\n";
   std::cout << "\\tikzstyle{kaedge} = [draw,thick,=>,color=blue]\n";
   std::cout << "\\tikzstyle{kbedge} = [draw,thick,=>,color=pinegreen!25]\n";
   
   std::vector<_MDD> queued;
   queued.push_back(r);
   status[0] = 1;
   status[1] = 1;
   status[r] = 1;
   unsigned int head = 0;
   std::cout << "\\foreach \\pos/\\name/\\stat in {";
    
   bool first = true;
   
   int off = 0;
   unsigned int var = 0; 
   while( head < queued.size() )
   {
      _MDD n = queued[head];
      
      if(first)
      {
         first = false;
         std::cout << "{(0,0)/1/T}";
      }
      std::cout << ",";

      if( var != nodes[n][1] )
      {
         var = nodes[n][1];
         off = 0;
      }

      std::cout << "{(" << off << "," << 1.5*(nvars - nodes[n][1]) << ")/" << n << "/" << nodes[n][1] << "}";
      off += 2;

      for( unsigned int j = 2; j < nodes[n][0]; j += 2 )
      {
         if( status[nodes[n][j+1]] == 0 )
         {
            status[nodes[n][j+1]] = 1;
            queued.push_back(nodes[n][j+1]);
         }
      }
      head++;
   }
   std::cout << "}\n\t\t\\node[vertex] (\\name) at \\pos {$x_{\\stat}$};\n";

   std::cout << "\\foreach \\source/\\dest/\\label in {";
   
   first = true;
   for( unsigned int i = 0; i < queued.size(); i++ )
   {
      _MDD n = queued[i];


      for( unsigned int j = 2; j < nodes[n][0]; j += 2 )
      {
         if(first)
         {
            first = false;
         } else {
            std::cout << ",";
         }

         std::cout << "{" << n << "/" << nodes[n][j+1] << "/" << nodes[n][j] << "}" ;
      }
   }
   std::cout << "}\n\t\t\\path[edge] (\\source) -- node {$\\label$} (\\dest);\n";

   std::cout << "\\end{tikzpicture}\n";
   std::cout << "\\end{document}\n";
#endif
}

void MDDTable::print_dot(_MDD r)
{
  return;
#if 0
  if(r < 2)
    return;

  std::cout << "digraph ingraph { graph [ranksep=\"1.0 equally\"] " << std::endl;
  
  std::vector<int> queued;
  queued.push_back(r);

  status[r] = 1;
  int nextid = 2;
  unsigned int head = 0;
  
  for(head = 0; head < queued.size(); head++ )
  {
    int n_id = queued[head];
    MDDNodeEl* node(nodes[n_id]);
    printf("  { node [shape=record label=\"{<prefix>%d: x%d | {",n_id,node->var);

    bool first = true;
    for( unsigned int ii = 0; ii < nodes[n_id]->sz; ii++ )
    {
      if( first )
        first = false;
      else
        printf("|");
      
      printf("<p%d>",ii);
      if(node->edges[ii].dest < 2)
      {
        if( node->edges[ii].dest == MDDTRUE )
        {
          printf("T");
        } else {
          assert(node->edges[ii].dest == MDDFALSE);
          printf("F");
        }
      } else {
        if(!status[node->edges[ii].dest])
        {
          status[node->edges[ii].dest] = nextid++;
          queued.push_back(node->edges[ii].dest);
        }
        printf("%d",node->edges[ii].dest);
      }
    }
    printf("} }\"] %d };\n", n_id);
  }
  
  for(head = 0; head < queued.size(); head++ )
  {
    int n_id = queued[head];
    MDDNodeEl* node(nodes[n_id]);

    if(!(node->low < 2))
    {
      printf("\t%d:pL -> %d;\n",n_id,node->low);
    }

    for( unsigned int ii = 0; ii < node->sz; ii++ )
    {
      if( !(node->edges[ii].dest < 2) )
      {
        printf("\t%d:p%d -> %d;\n",n_id,ii,node->edges[ii].dest);
      }
    }
  }
  std::cout << "};" << std::endl;
  for( unsigned int ii = 0; ii < queued.size(); ii++ )
    status[queued[ii]] = 0;
#endif
}

MDD operator| (const MDD& a, const MDD& b) {
  assert( a.table == b.table );
  return MDD(a.table, a.table->mdd_or(a.val,b.val));  
}

MDD operator& (const MDD& a, const MDD& b) {
  assert( a.table == b.table);
  return MDD(a.table, a.table->mdd_and(a.val,b.val));
}

MDD operator^ (const MDD& a, const MDD& b) {
  assert( a.table == b.table);
  assert(0); // NOT IMPLEMENTED

  return MDD(a.table, MDDFALSE);
}

MDD mdd_iff(const MDD& a, const MDD& b) {
  assert( a.table == b.table);
  assert(0); // NOT IMPLEMENTED

  return MDD(a.table, MDDFALSE);
}

MDD operator~(const MDD& r) {
  return MDD(r.table, r.table->mdd_not(r.val));
}

bool operator <= (const MDD& a, const MDD& b)
{
  assert( a.table == b.table);
  return a.table->mdd_leq(a.val, b.val);
}

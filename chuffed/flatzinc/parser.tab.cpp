/* A Bison parser, made by GNU Bison 3.0.4.  */

/* Bison implementation for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015 Free Software Foundation, Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "3.0.4"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 1

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1




/* Copy the first part of user declarations.  */
#line 26 "parser.yxx" /* yacc.c:339  */

#define YYPARSE_PARAM parm
#define YYLEX_PARAM static_cast<ParserState*>(parm)->yyscanner

#include <iostream>
#include <fstream>
#include <sstream>

#include <chuffed/flatzinc/flatzinc.h>
#include <chuffed/flatzinc/parser.tab.h>

#ifdef HAVE_MMAP
#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/mman.h>
#include <sys/stat.h>
#endif

using namespace std;

int yyparse(void*);
int yylex(YYSTYPE*, void* scanner);
int yylex_init (void** scanner);
int yylex_destroy (void* scanner);
int yyget_lineno (void* scanner);
void yyset_extra (void* user_defined ,void* yyscanner );

extern int yydebug;

using namespace FlatZinc;

void yyerror(void* parm, const char *str) {
  ParserState* pp = static_cast<ParserState*>(parm);
  pp->err << "Error: " << str
          << " in line no. " << yyget_lineno(pp->yyscanner)
          << std::endl;
  pp->hadError = true;
}

void yyassert(ParserState* pp, bool cond, const char* str)
{
  if (!cond) {
    pp->err << "Error: " << str
            << " in line no. " << yyget_lineno(pp->yyscanner)
            << std::endl;
    pp->hadError = true;
  }
}

/*
 * The symbol tables
 *
 */

AST::Node* getArrayElement(ParserState* pp, string id, unsigned int offset) {
  if (offset > 0) {
    vector<int> tmp;
    if (pp->intvararrays.get(id, tmp) && offset<=tmp.size())
      return new AST::IntVar(tmp[offset-1]);
    if (pp->boolvararrays.get(id, tmp) && offset<=tmp.size())
      return new AST::BoolVar(tmp[offset-1]);
    if (pp->setvararrays.get(id, tmp) && offset<=tmp.size())
      return new AST::SetVar(tmp[offset-1]);

    if (pp->intvalarrays.get(id, tmp) && offset<=tmp.size())
      return new AST::IntLit(tmp[offset-1]);
    if (pp->boolvalarrays.get(id, tmp) && offset<=tmp.size())
      return new AST::BoolLit(tmp[offset-1]);
    vector<AST::SetLit> tmpS;
    if (pp->setvalarrays.get(id, tmpS) && offset<=tmpS.size())
      return new AST::SetLit(tmpS[offset-1]);    
  }

  pp->err << "Error: array access to " << id << " invalid"
          << " in line no. "
          << yyget_lineno(pp->yyscanner) << std::endl;
  pp->hadError = true;
  return new AST::IntVar(0); // keep things consistent
}
AST::Node* getVarRefArg(ParserState* pp, string id, bool annotation = false) {
  int tmp;
  if (pp->intvarTable.get(id, tmp))
    return new AST::IntVar(tmp);
  if (pp->boolvarTable.get(id, tmp))
    return new AST::BoolVar(tmp);
  if (pp->setvarTable.get(id, tmp))
    return new AST::SetVar(tmp);
  if (annotation)
    return new AST::Atom(id);
  pp->err << "Error: undefined variable " << id
          << " in line no. "
          << yyget_lineno(pp->yyscanner) << std::endl;
  pp->hadError = true;
  return new AST::IntVar(0); // keep things consistent
}

void addDomainConstraint(ParserState* pp, std::string id, AST::Node* var,
                         Option<AST::SetLit* >& dom) {
  if (!dom())
    return;
  AST::Array* args = new AST::Array(2);
  args->a[0] = var;
  args->a[1] = dom.some();
  pp->domainConstraints.push_back(new ConExpr(id, args));
}

/*
 * Initialize the root gecode space
 *
 */

void initfg(ParserState* pp) {
#if EXPOSE_INT_LITS
  static struct {
    const char *int_CMP_reif;
    IntRelType irt;
  } int_CMP_table[] = {
    { "int_eq_reif", IRT_EQ },
    { "int_ne_reif", IRT_NE },
    { "int_ge_reif", IRT_GE },
    { "int_gt_reif", IRT_GT },
    { "int_le_reif", IRT_LE },
    { "int_lt_reif", IRT_LT }
  };

  for (int i = 0; i < static_cast<int>(pp->domainConstraints2.size()); ) {
    ConExpr& c = *pp->domainConstraints2[i].first;
    for (int j = 0; j < 6; ++j)
      if (c.id.compare(int_CMP_table[j].int_CMP_reif) == 0) {
        if (!c[2]->isBoolVar())
          goto not_found;
        int k;
        for (k = c[2]->getBoolVar(); pp->boolvars[k].second->alias; k = pp->boolvars[k].second->i)
          ;
        BoolVarSpec& boolvar = *static_cast<BoolVarSpec *>(pp->boolvars[k].second);
        if (boolvar.alias_var >= 0)
          goto not_found;
        if (c[0]->isIntVar() && c[1]->isInt(boolvar.alias_val)) {
          boolvar.alias_var = c[0]->getIntVar();
          boolvar.alias_irt = int_CMP_table[j].irt;
          goto found;
        }
        if (c[1]->isIntVar() && c[0]->isInt(boolvar.alias_val)) {
          boolvar.alias_var = c[1]->getIntVar();
          boolvar.alias_irt = -int_CMP_table[j].irt;
          goto found;
        }
      }
  not_found:
    ++i;
    continue;
  found:
    delete pp->domainConstraints2[i].first;
    delete pp->domainConstraints2[i].second;
    pp->domainConstraints2.erase(pp->domainConstraints2.begin() + i);
  }
#endif

  if (!pp->hadError)
    pp->fg = new FlatZincSpace(pp->intvars.size(),
                                pp->boolvars.size(),
                                pp->setvars.size());

  for (unsigned int i=0; i<pp->intvars.size(); i++) {
 //fprintf(stderr, "v%d=%s\n", i, pp->intvars[i].first.c_str());
    if (!pp->hadError) {
      try {
        pp->fg->newIntVar(static_cast<IntVarSpec*>(pp->intvars[i].second));
        IntVar* newiv = pp->fg->iv[pp->fg->intVarCount-1];
        // std::cerr << "created new int var for " << (pp->intvars[i].first) << ": " << newiv << "\n";
        intVarString.insert(std::pair<IntVar*, std::string>(newiv, pp->intvars[i].first));
      } catch (FlatZinc::Error& e) {
        yyerror(pp, e.toString().c_str());
      }
    }
    if (pp->intvars[i].first[0] != '[') {
      delete pp->intvars[i].second;
      pp->intvars[i].second = NULL;
    }
  }
  for (unsigned int i=0; i<pp->boolvars.size(); i++) {
    if (!pp->hadError) {
      try {
        pp->fg->newBoolVar(
          static_cast<BoolVarSpec*>(pp->boolvars[i].second));
        BoolView newiv = pp->fg->bv[pp->fg->boolVarCount-1];
        if (pp->boolvars[i].second->assigned)
          boolVarString.insert(std::pair<BoolView, std::string>(newiv, "ASSIGNED_AT_ROOT"));
        else
          boolVarString.insert(std::pair<BoolView, std::string>(newiv, pp->boolvars[i].first));
        string label;
        label = pp->boolvars[i].first;
        label.append("=true");
        litString.insert(std::pair<int,std::string>(toInt(newiv.getLit(true)), label));
        label = pp->boolvars[i].first;
        label.append("=false");
        litString.insert(std::pair<int,std::string>(toInt(newiv.getLit(false)), label));
      } catch (FlatZinc::Error& e) {
        yyerror(pp, e.toString().c_str());
      }
    }
    if (pp->boolvars[i].first[0] != '[') {
      delete pp->boolvars[i].second;
      pp->boolvars[i].second = NULL;
    }
  }
  for (unsigned int i=0; i<pp->setvars.size(); i++) {
    if (!pp->hadError) {
      try {
        pp->fg->newSetVar(static_cast<SetVarSpec*>(pp->setvars[i].second));
      } catch (FlatZinc::Error& e) {
        yyerror(pp, e.toString().c_str());
      }
    }      
    if (pp->setvars[i].first[0] != '[') {
      delete pp->setvars[i].second;
      pp->setvars[i].second = NULL;
    }
  }
  for (unsigned int i=pp->domainConstraints.size(); i--;) {
    if (!pp->hadError) {
      try {
        assert(pp->domainConstraints[i]->args->a.size() == 2);
        pp->fg->postConstraint(*pp->domainConstraints[i], NULL);
        delete pp->domainConstraints[i];
      } catch (FlatZinc::Error& e) {
        yyerror(pp, e.toString().c_str());        
      }
    }
  }
#if EXPOSE_INT_LITS
  for (int i = 0; i < static_cast<int>(pp->domainConstraints2.size()); ++i) {
    if (!pp->hadError) {
      try {
        pp->fg->postConstraint(*pp->domainConstraints2[i].first, pp->domainConstraints2[i].second);
        delete pp->domainConstraints2[i].first;
        delete pp->domainConstraints2[i].second;
      } catch (FlatZinc::Error& e) {
        yyerror(pp, e.toString().c_str());        
      }
    }
  }
#endif
}

AST::Node* arrayOutput(AST::Call* ann) {
  AST::Array* a = NULL;
  
  if (ann->args->isArray()) {
    a = ann->args->getArray();
  } else {
    a = new AST::Array(ann->args);
  }
  
  std::ostringstream oss;
  
  oss << "array" << a->a.size() << "d(";
  for (unsigned int i=0; i<a->a.size(); i++) {
    AST::SetLit* s = a->a[i]->getSet();
    if (s->empty())
      oss << "{}, ";
    else if (s->interval)
      oss << s->min << ".." << s->max << ", ";
    else {
      oss << "{";
      for (unsigned int j=0; j<s->s.size(); j++) {
        oss << s->s[j];
        if (j<s->s.size()-1)
          oss << ",";
      }
      oss << "}, ";
    }
  }

  if (!ann->args->isArray()) {
    a->a[0] = NULL;
    delete a;
  }
  return new AST::String(oss.str());
}

/*
 * The main program
 *
 */

namespace FlatZinc {

  void solve(const std::string& filename, std::ostream& err) {
#ifdef HAVE_MMAP
    int fd;
    char* data;
    struct stat sbuf;
    fd = open(filename.c_str(), O_RDONLY);
    if (fd == -1) {
      err << "Cannot open file " << filename << endl;
      exit(0);
    }
    if (stat(filename.c_str(), &sbuf) == -1) {
      err << "Cannot stat file " << filename << endl;
      return;      
    }
    data = (char*)mmap((caddr_t)0, sbuf.st_size, PROT_READ, MAP_SHARED, fd,0);
    if (data == (caddr_t)(-1)) {
      err << "Cannot mmap file " << filename << endl;
      return;      
    }

    ParserState pp(data, sbuf.st_size, err);
#else
    std::ifstream file;
    file.open(filename.c_str());
    if (!file.is_open()) {
      err << "Cannot open file " << filename << endl;
      exit(0);
    }
    std::string s = string(istreambuf_iterator<char>(file),
                           istreambuf_iterator<char>());
    ParserState pp(s, err);
#endif
    yylex_init(&pp.yyscanner);
    yyset_extra(&pp, pp.yyscanner);
    // yydebug = 1;
    yyparse(&pp);
		FlatZinc::s->output = pp.getOutput();
		FlatZinc::s->setOutput();
    
    if (pp.yyscanner)
      yylex_destroy(pp.yyscanner);
		if (pp.hadError) abort();
  }

  void solve(std::istream& is, std::ostream& err) {
    std::string s = string(istreambuf_iterator<char>(is),
                           istreambuf_iterator<char>());

    ParserState pp(s, err);
    yylex_init(&pp.yyscanner);
    yyset_extra(&pp, pp.yyscanner);
    // yydebug = 1;
    yyparse(&pp);
    FlatZinc::s->output = pp.getOutput();
    
    if (pp.yyscanner)
      yylex_destroy(pp.yyscanner);
		if (pp.hadError) abort();
  }

}


#line 421 "parser.tab.c" /* yacc.c:339  */

# ifndef YY_NULLPTR
#  if defined __cplusplus && 201103L <= __cplusplus
#   define YY_NULLPTR nullptr
#  else
#   define YY_NULLPTR 0
#  endif
# endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 1
#endif


/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int yydebug;
#endif

/* Token type.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    INT_LIT = 258,
    BOOL_LIT = 259,
    FLOAT_LIT = 260,
    ID = 261,
    STRING_LIT = 262,
    VAR = 263,
    PAR = 264,
    ANNOTATION = 265,
    ANY = 266,
    ARRAY = 267,
    BOOLTOK = 268,
    CASE = 269,
    COLONCOLON = 270,
    CONSTRAINT = 271,
    DEFAULT = 272,
    DOTDOT = 273,
    ELSE = 274,
    ELSEIF = 275,
    ENDIF = 276,
    ENUM = 277,
    FLOATTOK = 278,
    FUNCTION = 279,
    IF = 280,
    INCLUDE = 281,
    INTTOK = 282,
    LET = 283,
    MAXIMIZE = 284,
    MINIMIZE = 285,
    OF = 286,
    SATISFY = 287,
    OUTPUT = 288,
    PREDICATE = 289,
    RECORD = 290,
    SET = 291,
    SHOW = 292,
    SHOWCOND = 293,
    SOLVE = 294,
    STRING = 295,
    TEST = 296,
    THEN = 297,
    TUPLE = 298,
    TYPE = 299,
    VARIANT_RECORD = 300,
    WHERE = 301
  };
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED

union YYSTYPE
{
#line 381 "parser.yxx" /* yacc.c:355  */
 int iValue; char* sValue; bool bValue; double dValue;
         std::vector<int>* setValue;
         FlatZinc::AST::SetLit* setLit;
         std::vector<double>* floatSetValue;
         std::vector<FlatZinc::AST::SetLit>* setValueList;
         FlatZinc::Option<FlatZinc::AST::SetLit* > oSet;
         FlatZinc::VarSpec* varSpec;
         FlatZinc::Option<FlatZinc::AST::Node*> oArg;
         std::vector<FlatZinc::VarSpec*>* varSpecVec;
         FlatZinc::Option<std::vector<FlatZinc::VarSpec*>* > oVarSpecVec;
         FlatZinc::AST::Node* arg;
         FlatZinc::AST::Array* argVec;
       

#line 520 "parser.tab.c" /* yacc.c:355  */
};

typedef union YYSTYPE YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif



int yyparse (void *parm);



/* Copy the second part of user declarations.  */

#line 536 "parser.tab.c" /* yacc.c:358  */

#ifdef short
# undef short
#endif

#ifdef YYTYPE_UINT8
typedef YYTYPE_UINT8 yytype_uint8;
#else
typedef unsigned char yytype_uint8;
#endif

#ifdef YYTYPE_INT8
typedef YYTYPE_INT8 yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef YYTYPE_UINT16
typedef YYTYPE_UINT16 yytype_uint16;
#else
typedef unsigned short int yytype_uint16;
#endif

#ifdef YYTYPE_INT16
typedef YYTYPE_INT16 yytype_int16;
#else
typedef short int yytype_int16;
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif ! defined YYSIZE_T
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned int
# endif
#endif

#define YYSIZE_MAXIMUM ((YYSIZE_T) -1)

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif

#ifndef YY_ATTRIBUTE
# if (defined __GNUC__                                               \
      && (2 < __GNUC__ || (__GNUC__ == 2 && 96 <= __GNUC_MINOR__)))  \
     || defined __SUNPRO_C && 0x5110 <= __SUNPRO_C
#  define YY_ATTRIBUTE(Spec) __attribute__(Spec)
# else
#  define YY_ATTRIBUTE(Spec) /* empty */
# endif
#endif

#ifndef YY_ATTRIBUTE_PURE
# define YY_ATTRIBUTE_PURE   YY_ATTRIBUTE ((__pure__))
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# define YY_ATTRIBUTE_UNUSED YY_ATTRIBUTE ((__unused__))
#endif

#if !defined _Noreturn \
     && (!defined __STDC_VERSION__ || __STDC_VERSION__ < 201112)
# if defined _MSC_VER && 1200 <= _MSC_VER
#  define _Noreturn __declspec (noreturn)
# else
#  define _Noreturn YY_ATTRIBUTE ((__noreturn__))
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(E) ((void) (E))
#else
# define YYUSE(E) /* empty */
#endif

#if defined __GNUC__ && 407 <= __GNUC__ * 100 + __GNUC_MINOR__
/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN \
    _Pragma ("GCC diagnostic push") \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")\
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# define YY_IGNORE_MAYBE_UNINITIALIZED_END \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif


#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
      /* Use EXIT_SUCCESS as a witness for stdlib.h.  */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
             && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss_alloc;
  YYSTYPE yyvs_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYSIZE_T yynewbytes;                                            \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / sizeof (*yyptr);                          \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, (Count) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYSIZE_T yyi;                         \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  7
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   342

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  57
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  66
/* YYNRULES -- Number of rules.  */
#define YYNRULES  155
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  338

/* YYTRANSLATE[YYX] -- Symbol number corresponding to YYX as returned
   by yylex, with out-of-bounds checking.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   301

#define YYTRANSLATE(YYX)                                                \
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, without out-of-bounds checking.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
      48,    49,     2,     2,    50,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,    51,    47,
       2,    54,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,    52,     2,    53,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    55,     2,    56,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46
};

#if YYDEBUG
  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,   480,   480,   482,   484,   487,   488,   492,   497,   505,
     506,   510,   515,   523,   524,   531,   533,   535,   538,   539,
     542,   545,   546,   547,   548,   551,   552,   553,   554,   557,
     558,   561,   562,   569,   600,   630,   635,   666,   690,   699,
     711,   770,   822,   829,   884,   897,   910,   917,   931,   935,
     950,   974,   975,   979,   981,   984,   984,   986,   990,   992,
    1007,  1031,  1032,  1036,  1038,  1042,  1046,  1048,  1063,  1087,
    1088,  1092,  1094,  1097,  1100,  1102,  1117,  1141,  1142,  1146,
    1148,  1151,  1156,  1157,  1162,  1163,  1168,  1169,  1174,  1175,
    1179,  1197,  1218,  1240,  1248,  1265,  1267,  1269,  1275,  1277,
    1290,  1291,  1298,  1300,  1307,  1308,  1312,  1314,  1319,  1320,
    1324,  1326,  1331,  1332,  1336,  1338,  1343,  1344,  1348,  1350,
    1358,  1360,  1364,  1366,  1371,  1372,  1376,  1378,  1380,  1382,
    1384,  1433,  1447,  1448,  1452,  1454,  1462,  1473,  1495,  1496,
    1504,  1505,  1509,  1511,  1515,  1519,  1523,  1525,  1529,  1531,
    1535,  1537,  1539,  1541,  1543,  1586
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || 1
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "INT_LIT", "BOOL_LIT", "FLOAT_LIT", "ID",
  "STRING_LIT", "VAR", "PAR", "ANNOTATION", "ANY", "ARRAY", "BOOLTOK", "CASE",
  "COLONCOLON", "CONSTRAINT", "DEFAULT", "DOTDOT", "ELSE", "ELSEIF",
  "ENDIF", "ENUM", "FLOATTOK", "FUNCTION", "IF", "INCLUDE", "INTTOK", "LET",
  "MAXIMIZE", "MINIMIZE", "OF", "SATISFY", "OUTPUT", "PREDICATE", "RECORD",
  "SET", "SHOW", "SHOWCOND", "SOLVE", "STRING", "TEST", "THEN", "TUPLE",
  "TYPE", "VARIANT_RECORD", "WHERE", "';'", "'('", "')'", "','", "':'",
  "'['", "']'", "'='", "'{'", "'}'", "$accept", "model", "preddecl_items",
  "preddecl_items_head", "vardecl_items", "vardecl_items_head",
  "constraint_items", "constraint_items_head", "preddecl_item",
  "pred_arg_list", "pred_arg_list_head", "pred_arg", "pred_arg_type",
  "pred_arg_simple_type", "pred_array_init", "pred_array_init_arg",
  "vardecl_item", "int_init", "int_init_list", "int_init_list_head",
  "list_tail", "int_var_array_literal", "float_init", "float_init_list",
  "float_init_list_head", "float_var_array_literal", "bool_init",
  "bool_init_list", "bool_init_list_head", "bool_var_array_literal",
  "set_init", "set_init_list", "set_init_list_head",
  "set_var_array_literal", "vardecl_int_var_array_init",
  "vardecl_bool_var_array_init", "vardecl_float_var_array_init",
  "vardecl_set_var_array_init", "constraint_item", "solve_item",
  "int_ti_expr_tail", "bool_ti_expr_tail", "float_ti_expr_tail",
  "set_literal", "int_list", "int_list_head", "bool_list",
  "bool_list_head", "float_list", "float_list_head", "set_literal_list",
  "set_literal_list_head", "flat_expr_list", "flat_expr",
  "non_array_expr_opt", "non_array_expr", "non_array_expr_list",
  "non_array_expr_list_head", "solve_expr", "minmax", "annotations",
  "annotations_head", "annotation", "annotation_list", "annotation_expr",
  "ann_non_array_expr", YY_NULLPTR
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[NUM] -- (External) token number corresponding to the
   (internal) symbol number NUM (which must be that of a token).  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298,   299,   300,   301,    59,    40,    41,
      44,    58,    91,    93,    61,   123,   125
};
# endif

#define YYPACT_NINF -122

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-122)))

#define YYTABLE_NINF -1

#define yytable_value_is_error(Yytable_value) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int16 yypact[] =
{
     -23,    11,    28,    44,   -23,     1,     5,  -122,    41,    98,
      10,    32,  -122,    58,    93,    78,    44,    66,    73,    70,
    -122,    37,   126,  -122,  -122,   118,   142,    88,   111,   112,
     161,   159,    27,  -122,   110,   117,   162,   130,    78,   128,
     133,  -122,   167,  -122,    99,   131,  -122,  -122,   153,   136,
     137,  -122,   135,  -122,  -122,  -122,    27,  -122,  -122,   138,
     140,   186,   187,   188,   177,   181,   146,  -122,   195,  -122,
      75,   181,   152,   157,  -122,  -122,   181,  -122,     9,    27,
    -122,    37,  -122,   194,   151,   202,   154,   203,   156,   181,
     181,   181,   204,   100,   160,   196,   207,  -122,   127,   206,
    -122,    56,  -122,  -122,   164,   197,  -122,    90,  -122,  -122,
    -122,  -122,   210,  -122,  -122,  -122,  -122,   168,   168,   168,
     171,   208,  -122,  -122,   -32,   100,    93,  -122,  -122,  -122,
    -122,    20,   100,   181,   208,  -122,  -122,   169,    20,  -122,
     -12,  -122,  -122,   172,  -122,  -122,  -122,   221,    20,   226,
       9,   199,   181,    20,  -122,  -122,  -122,   200,   229,   100,
     104,  -122,    91,   178,  -122,  -122,   182,    20,  -122,   184,
     190,   181,   127,   181,   189,  -122,  -122,  -122,  -122,    38,
     168,  -122,    64,  -122,   108,   191,   192,   100,  -122,  -122,
      20,   193,  -122,    20,  -122,  -122,  -122,  -122,   239,    99,
    -122,  -122,   115,   198,   201,   213,   205,  -122,  -122,  -122,
    -122,  -122,  -122,   211,  -122,   216,   209,   212,   214,   242,
     244,    27,   245,  -122,    27,   247,   248,   249,   181,   181,
     217,   181,   218,   181,   181,   181,   219,   220,   251,   222,
     252,   223,   224,   225,   215,   228,   181,   230,   181,   231,
    -122,   232,  -122,   233,  -122,   255,   256,   227,    93,   234,
      15,  -122,   144,  -122,   155,  -122,   236,   138,   237,   140,
     235,   238,   240,  -122,  -122,   241,  -122,   243,   250,  -122,
     246,  -122,   253,   254,  -122,   257,  -122,   258,   260,  -122,
    -122,  -122,  -122,    24,  -122,    60,  -122,   267,  -122,    15,
    -122,   268,  -122,   144,  -122,   269,  -122,   155,  -122,   208,
    -122,   259,   263,   262,  -122,   264,   265,  -122,   266,  -122,
     270,  -122,   271,  -122,  -122,    24,  -122,   272,  -122,    60,
    -122,  -122,  -122,  -122,  -122,   273,  -122,  -122
};

  /* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
     Performed when YYTABLE does not specify something else to do.  Zero
     means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       3,     0,     0,     7,     4,     0,     0,     1,     0,     0,
       0,     0,    95,     0,   104,    11,     8,     0,     0,     0,
       5,    16,     0,    98,   100,     0,   104,     0,     0,     0,
       0,     0,     0,   106,     0,    55,     0,     0,    12,     0,
       0,     9,     0,     6,     0,     0,    27,    28,     0,     0,
      55,    18,     0,    24,    25,    97,     0,   110,   114,    55,
      55,     0,     0,     0,     0,   140,     0,    96,    56,   105,
     140,   140,     0,     0,    13,    10,   140,    23,     0,     0,
      15,    56,    17,     0,     0,    56,     0,    56,     0,   140,
     140,   140,     0,     0,     0,   141,     0,   107,     0,     0,
      91,     0,     2,    14,     0,     0,    31,     0,    29,    26,
      19,    20,     0,   111,    99,   115,   101,   124,   124,   124,
       0,   151,   150,   152,   154,     0,   104,   153,   142,   145,
     148,     0,     0,   140,   127,   126,   128,   130,   132,   129,
       0,   120,   122,     0,   139,   138,    93,     0,     0,     0,
       0,     0,   140,     0,    33,    34,    35,     0,     0,     0,
       0,   146,     0,     0,    38,   143,     0,     0,   134,     0,
      55,   140,     0,   140,   136,    94,    37,    32,    30,     0,
     124,   125,     0,   103,     0,   154,     0,     0,   149,   102,
       0,     0,   123,    56,   133,    90,   121,    92,     0,     0,
      21,    36,     0,     0,     0,     0,     0,   144,   155,   147,
      39,   131,   135,     0,    22,     0,     0,     0,     0,     0,
       0,     0,     0,   137,     0,     0,     0,     0,   140,   140,
       0,   140,     0,   140,   140,   140,     0,     0,     0,     0,
       0,    82,    84,    86,     0,     0,   140,     0,   140,     0,
      40,     0,    41,     0,    42,   108,   112,     0,   104,    88,
      51,    83,    69,    85,    61,    87,     0,    55,     0,    55,
       0,     0,     0,    43,    48,    49,    53,     0,    55,    66,
      67,    71,     0,    55,    58,    59,    63,     0,    55,    45,
     109,    46,   113,   116,    44,    77,    89,     0,    57,    56,
      52,     0,    73,    56,    70,     0,    65,    56,    62,     0,
     118,     0,    55,    75,    79,     0,    55,    74,     0,    54,
       0,    72,     0,    64,    47,    56,   117,     0,    81,    56,
      78,    50,    68,    60,   119,     0,    80,    76
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -122,  -122,  -122,  -122,  -122,  -122,  -122,  -122,   282,  -122,
    -122,   261,  -122,   -43,  -122,   145,   278,    -2,  -122,  -122,
     -50,  -122,    -8,  -122,  -122,  -122,     0,  -122,  -122,  -122,
     -28,  -122,  -122,  -122,  -122,  -122,  -122,  -122,   280,  -122,
      -1,   103,   105,   -90,  -121,  -122,  -122,    47,  -122,    52,
    -122,  -122,  -122,   148,  -112,  -109,  -122,  -122,  -122,  -122,
     -57,  -122,   -89,   163,  -122,   165
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     2,     3,     4,    15,    16,    37,    38,     5,    49,
      50,    51,    52,    53,   107,   108,    17,   276,   277,   278,
      69,   261,   286,   287,   288,   265,   281,   282,   283,   263,
     314,   315,   316,   296,   250,   252,   254,   273,    39,    72,
      54,    28,    29,   139,    34,    35,   266,    59,   268,    60,
     311,   312,   140,   141,   154,   142,   169,   170,   175,   147,
      94,    95,   161,   162,   129,   130
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_uint16 yytable[] =
{
      82,    77,    18,   127,   128,   163,   155,   156,    27,    86,
      88,     1,   105,   100,   101,    18,   159,     6,   274,   104,
     160,   275,   164,   134,   135,   136,   137,   309,     7,   168,
       8,    66,   117,   118,   119,   127,   106,   171,   172,   176,
       8,     8,   127,   165,   181,    44,   199,     8,    20,    45,
      46,    46,     9,    21,    12,    84,    10,    11,   191,    22,
      47,    47,    30,   309,    12,    12,   313,     8,   201,   127,
     127,    12,   202,    48,    48,   126,   166,   203,   109,   126,
      13,   210,    14,    31,   212,   144,   145,   204,   146,    32,
      93,    12,    14,    14,    36,   180,    33,   127,   209,    14,
     205,     8,     8,   121,   122,   123,   124,   121,   122,   123,
     185,    23,    46,    41,   195,   126,   197,    43,     8,    14,
     194,    24,    47,    98,    42,    12,    12,    99,    23,    55,
     134,   135,   136,   137,    25,    48,   200,   271,    24,    61,
     150,   187,    12,   151,   188,    33,    57,    58,   279,    56,
     280,   215,   125,    26,    14,   126,   214,   207,   187,   126,
     284,   285,    62,    63,    64,    65,    67,    68,    70,    71,
      26,   236,   237,    76,   239,    74,   241,   242,   243,   138,
      75,   206,   126,    78,    79,    80,    83,    81,    85,   257,
      87,   259,    89,    90,    91,    92,    93,    96,    97,   102,
     111,   216,   112,   310,   103,   317,   113,   120,   115,   143,
     114,   132,   116,   133,   131,   149,   152,   290,   148,   292,
     230,   167,   153,   232,   157,   173,   158,   174,   300,   177,
     179,   182,   183,   304,   189,   334,   190,   192,   308,   317,
     193,   198,   213,   160,   221,   208,   211,   224,   228,   219,
     229,   231,   220,   233,   234,   235,   222,   246,   248,    57,
     225,    58,   326,   226,   223,   227,   330,   255,   238,   240,
     318,   320,   322,   244,   245,   335,   247,   249,   251,   253,
     256,   270,   258,   260,   262,   264,    19,   293,   272,   289,
     291,   294,   295,   297,    40,   178,   298,   319,   301,   323,
     299,   336,   267,   321,   303,   217,   302,   218,   269,   305,
     307,   306,   324,   325,   327,   329,     0,   328,    73,   331,
     196,     0,   184,   332,   333,   186,   337,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   110
};

static const yytype_int16 yycheck[] =
{
      50,    44,     3,    93,    93,   126,   118,   119,     9,    59,
      60,    34,     3,    70,    71,    16,    48,     6,     3,    76,
      52,     6,   131,     3,     4,     5,     6,     3,     0,   138,
       3,    32,    89,    90,    91,   125,    27,    49,    50,   148,
       3,     3,   132,   132,   153,     8,     8,     3,    47,    12,
      13,    13,     8,    48,    27,    56,    12,    13,   167,    18,
      23,    23,    52,     3,    27,    27,     6,     3,   180,   159,
     160,    27,     8,    36,    36,    55,   133,    13,    79,    55,
      36,   190,    55,    51,   193,    29,    30,    23,    32,    31,
      15,    27,    55,    55,    16,   152,     3,   187,   187,    55,
      36,     3,     3,     3,     4,     5,     6,     3,     4,     5,
       6,    13,    13,    47,   171,    55,   173,    47,     3,    55,
     170,    23,    23,    48,    51,    27,    27,    52,    13,     3,
       3,     4,     5,     6,    36,    36,   179,   258,    23,    51,
      50,    50,    27,    53,    53,     3,     4,     5,     4,    31,
       6,    36,    52,    55,    55,    55,   199,    49,    50,    55,
       5,     6,    51,    51,     3,     6,    56,    50,     6,    39,
      55,   228,   229,     6,   231,    47,   233,   234,   235,    52,
      47,   182,    55,    52,    31,    49,    51,    50,    50,   246,
      50,   248,     6,     6,     6,    18,    15,    51,     3,    47,
       6,   202,    51,   293,    47,   295,     4,     3,     5,     3,
      56,    15,    56,     6,    54,    18,     6,   267,    54,   269,
     221,    52,    54,   224,    53,    53,    18,     6,   278,     3,
      31,    31,     3,   283,    56,   325,    54,    53,   288,   329,
      50,    52,     3,    52,    31,    53,    53,    31,     6,    51,
       6,     6,    51,     6,     6,     6,    51,     6,     6,     4,
      51,     5,   312,    51,    53,    51,   316,    52,    51,    51,
       3,     3,     3,    54,    54,     3,    54,    54,    54,    54,
      52,    54,    52,    52,    52,    52,     4,    52,    54,    53,
      53,    53,    52,    52,    16,   150,    53,   299,    52,   307,
      50,   329,   255,   303,    50,   202,    53,   202,   256,    52,
      50,    53,    53,    50,    52,    50,    -1,    53,    38,    53,
     172,    -1,   159,    53,    53,   160,    53,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    81
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,    34,    58,    59,    60,    65,     6,     0,     3,     8,
      12,    13,    27,    36,    55,    61,    62,    73,    97,    65,
      47,    48,    18,    13,    23,    36,    55,    97,    98,    99,
      52,    51,    31,     3,   101,   102,    16,    63,    64,    95,
      73,    47,    51,    47,     8,    12,    13,    23,    36,    66,
      67,    68,    69,    70,    97,     3,    31,     4,     5,   104,
     106,    51,    51,    51,     3,     6,    97,    56,    50,    77,
       6,    39,    96,    95,    47,    47,     6,    70,    52,    31,
      49,    50,    77,    51,    97,    50,    77,    50,    77,     6,
       6,     6,    18,    15,   117,   118,    51,     3,    48,    52,
     117,   117,    47,    47,   117,     3,    27,    71,    72,    97,
      68,     6,    51,     4,    56,     5,    56,   117,   117,   117,
       3,     3,     4,     5,     6,    52,    55,   100,   119,   121,
     122,    54,    15,     6,     3,     4,     5,     6,    52,   100,
     109,   110,   112,     3,    29,    30,    32,   116,    54,    18,
      50,    53,     6,    54,   111,   111,   111,    53,    18,    48,
      52,   119,   120,   101,   112,   119,   117,    52,   112,   113,
     114,    49,    50,    53,     6,   115,   112,     3,    72,    31,
     117,   112,    31,     3,   120,     6,   122,    50,    53,    56,
      54,   112,    53,    50,    77,   117,   110,   117,    52,     8,
      70,   111,     8,    13,    23,    36,    97,    49,    53,   119,
     112,    53,   112,     3,    70,    36,    97,    98,    99,    51,
      51,    31,    51,    53,    31,    51,    51,    51,     6,     6,
      97,     6,    97,     6,     6,     6,   117,   117,    51,   117,
      51,   117,   117,   117,    54,    54,     6,    54,     6,    54,
      91,    54,    92,    54,    93,    52,    52,   117,    52,   117,
      52,    78,    52,    86,    52,    82,   103,   104,   105,   106,
      54,   101,    54,    94,     3,     6,    74,    75,    76,     4,
       6,    83,    84,    85,     5,     6,    79,    80,    81,    53,
      77,    53,    77,    52,    53,    52,    90,    52,    53,    50,
      77,    52,    53,    50,    77,    52,    53,    50,    77,     3,
     100,   107,   108,     6,    87,    88,    89,   100,     3,    74,
       3,    83,     3,    79,    53,    50,    77,    52,    53,    50,
      77,    53,    53,    53,   100,     3,    87,    53
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    57,    58,    59,    59,    60,    60,    61,    61,    62,
      62,    63,    63,    64,    64,    65,    66,    66,    67,    67,
      68,    69,    69,    69,    69,    70,    70,    70,    70,    71,
      71,    72,    72,    73,    73,    73,    73,    73,    73,    73,
      73,    73,    73,    73,    73,    73,    73,    73,    74,    74,
      74,    75,    75,    76,    76,    77,    77,    78,    79,    79,
      79,    80,    80,    81,    81,    82,    83,    83,    83,    84,
      84,    85,    85,    86,    87,    87,    87,    88,    88,    89,
      89,    90,    91,    91,    92,    92,    93,    93,    94,    94,
      95,    95,    95,    96,    96,    97,    97,    97,    98,    98,
      99,    99,   100,   100,   101,   101,   102,   102,   103,   103,
     104,   104,   105,   105,   106,   106,   107,   107,   108,   108,
     109,   109,   110,   110,   111,   111,   112,   112,   112,   112,
     112,   112,   113,   113,   114,   114,   115,   115,   116,   116,
     117,   117,   118,   118,   119,   119,   120,   120,   121,   121,
     122,   122,   122,   122,   122,   122
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     5,     0,     1,     2,     3,     0,     1,     2,
       3,     0,     1,     2,     3,     5,     0,     2,     1,     3,
       3,     6,     7,     2,     1,     1,     3,     1,     1,     1,
       3,     1,     3,     6,     6,     6,     8,     6,     6,     8,
      13,    13,    13,    15,    15,    15,    15,    17,     1,     1,
       4,     0,     2,     1,     3,     0,     1,     3,     1,     1,
       4,     0,     2,     1,     3,     3,     1,     1,     4,     0,
       2,     1,     3,     3,     1,     1,     4,     0,     2,     1,
       3,     3,     0,     2,     0,     2,     0,     2,     0,     2,
       6,     3,     6,     3,     4,     1,     3,     3,     1,     4,
       1,     4,     3,     3,     0,     2,     1,     3,     0,     2,
       1,     3,     0,     2,     1,     3,     0,     2,     1,     3,
       1,     3,     1,     3,     0,     2,     1,     1,     1,     1,
       1,     4,     0,     2,     1,     3,     1,     4,     1,     1,
       0,     1,     2,     3,     4,     1,     1,     3,     1,     3,
       1,     1,     1,     1,     1,     4
};


#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)
#define YYEMPTY         (-2)
#define YYEOF           0

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                  \
do                                                              \
  if (yychar == YYEMPTY)                                        \
    {                                                           \
      yychar = (Token);                                         \
      yylval = (Value);                                         \
      YYPOPSTACK (yylen);                                       \
      yystate = *yyssp;                                         \
      goto yybackup;                                            \
    }                                                           \
  else                                                          \
    {                                                           \
      yyerror (parm, YY_("syntax error: cannot back up")); \
      YYERROR;                                                  \
    }                                                           \
while (0)

/* Error token number */
#define YYTERROR        1
#define YYERRCODE       256



/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)

/* This macro is provided for backward compatibility. */
#ifndef YY_LOCATION_PRINT
# define YY_LOCATION_PRINT(File, Loc) ((void) 0)
#endif


# define YY_SYMBOL_PRINT(Title, Type, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Type, Value, parm); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*----------------------------------------.
| Print this symbol's value on YYOUTPUT.  |
`----------------------------------------*/

static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, void *parm)
{
  FILE *yyo = yyoutput;
  YYUSE (yyo);
  YYUSE (parm);
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# endif
  YYUSE (yytype);
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep, void *parm)
{
  YYFPRINTF (yyoutput, "%s %s (",
             yytype < YYNTOKENS ? "token" : "nterm", yytname[yytype]);

  yy_symbol_value_print (yyoutput, yytype, yyvaluep, parm);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yytype_int16 *yybottom, yytype_int16 *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yytype_int16 *yyssp, YYSTYPE *yyvsp, int yyrule, void *parm)
{
  unsigned long int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       yystos[yyssp[yyi + 1 - yynrhs]],
                       &(yyvsp[(yyi + 1) - (yynrhs)])
                                              , parm);
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, Rule, parm); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif


#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
static YYSIZE_T
yystrlen (const char *yystr)
{
  YYSIZE_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
yystpcpy (char *yydest, const char *yysrc)
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYSIZE_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYSIZE_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
        switch (*++yyp)
          {
          case '\'':
          case ',':
            goto do_not_strip_quotes;

          case '\\':
            if (*++yyp != '\\')
              goto do_not_strip_quotes;
            /* Fall through.  */
          default:
            if (yyres)
              yyres[yyn] = *yyp;
            yyn++;
            break;

          case '"':
            if (yyres)
              yyres[yyn] = '\0';
            return yyn;
          }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return yystrlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.

   Return 0 if *YYMSG was successfully written.  Return 1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return 2 if the
   required number of bytes is too large to store.  */
static int
yysyntax_error (YYSIZE_T *yymsg_alloc, char **yymsg,
                yytype_int16 *yyssp, int yytoken)
{
  YYSIZE_T yysize0 = yytnamerr (YY_NULLPTR, yytname[yytoken]);
  YYSIZE_T yysize = yysize0;
  enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULLPTR;
  /* Arguments of yyformat. */
  char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
  /* Number of reported tokens (one for the "unexpected", one per
     "expected"). */
  int yycount = 0;

  /* There are many possibilities here to consider:
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yytoken != YYEMPTY)
    {
      int yyn = yypact[*yyssp];
      yyarg[yycount++] = yytname[yytoken];
      if (!yypact_value_is_default (yyn))
        {
          /* Start YYX at -YYN if negative to avoid negative indexes in
             YYCHECK.  In other words, skip the first -YYN actions for
             this state because they are default actions.  */
          int yyxbegin = yyn < 0 ? -yyn : 0;
          /* Stay within bounds of both yycheck and yytname.  */
          int yychecklim = YYLAST - yyn + 1;
          int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
          int yyx;

          for (yyx = yyxbegin; yyx < yyxend; ++yyx)
            if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR
                && !yytable_value_is_error (yytable[yyx + yyn]))
              {
                if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                  {
                    yycount = 1;
                    yysize = yysize0;
                    break;
                  }
                yyarg[yycount++] = yytname[yyx];
                {
                  YYSIZE_T yysize1 = yysize + yytnamerr (YY_NULLPTR, yytname[yyx]);
                  if (! (yysize <= yysize1
                         && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
                    return 2;
                  yysize = yysize1;
                }
              }
        }
    }

  switch (yycount)
    {
# define YYCASE_(N, S)                      \
      case N:                               \
        yyformat = S;                       \
      break
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
# undef YYCASE_
    }

  {
    YYSIZE_T yysize1 = yysize + yystrlen (yyformat);
    if (! (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
      return 2;
    yysize = yysize1;
  }

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return 1;
    }

  /* Avoid sprintf, as that infringes on the user's name space.
     Don't have undefined behavior even if the translation
     produced a string with the wrong number of "%s"s.  */
  {
    char *yyp = *yymsg;
    int yyi = 0;
    while ((*yyp = *yyformat) != '\0')
      if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
        {
          yyp += yytnamerr (yyp, yyarg[yyi++]);
          yyformat += 2;
        }
      else
        {
          yyp++;
          yyformat++;
        }
  }
  return 0;
}
#endif /* YYERROR_VERBOSE */

/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep, void *parm)
{
  YYUSE (yyvaluep);
  YYUSE (parm);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YYUSE (yytype);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}




/*----------.
| yyparse.  |
`----------*/

int
yyparse (void *parm)
{
/* The lookahead symbol.  */
int yychar;


/* The semantic value of the lookahead symbol.  */
/* Default value used for initialization, for pacifying older GCCs
   or non-GCC compilers.  */
YY_INITIAL_VALUE (static YYSTYPE yyval_default;)
YYSTYPE yylval YY_INITIAL_VALUE (= yyval_default);

    /* Number of syntax errors so far.  */
    int yynerrs;

    int yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       'yyss': related to states.
       'yyvs': related to semantic values.

       Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* The state stack.  */
    yytype_int16 yyssa[YYINITDEPTH];
    yytype_int16 *yyss;
    yytype_int16 *yyssp;

    /* The semantic value stack.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs;
    YYSTYPE *yyvsp;

    YYSIZE_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken = 0;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yyssp = yyss = yyssa;
  yyvsp = yyvs = yyvsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY; /* Cause a token to be read.  */
  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyss + yystacksize - 1 <= yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
        /* Give user a chance to reallocate the stack.  Use copies of
           these so that the &'s don't force the real ones into
           memory.  */
        YYSTYPE *yyvs1 = yyvs;
        yytype_int16 *yyss1 = yyss;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * sizeof (*yyssp),
                    &yyvs1, yysize * sizeof (*yyvsp),
                    &yystacksize);

        yyss = yyss1;
        yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyexhaustedlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
        goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yytype_int16 *yyss1 = yyss;
        union yyalloc *yyptr =
          (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
        if (! yyptr)
          goto yyexhaustedlab;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
#  undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;

      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
                  (unsigned long int) yystacksize));

      if (yyss + yystacksize - 1 <= yyssp)
        YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid lookahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = yylex (&yylval, YYLEX_PARAM);
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token.  */
  yychar = YYEMPTY;

  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     '$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 7:
#line 492 "parser.yxx" /* yacc.c:1646  */
    {
#if !EXPOSE_INT_LITS
        initfg(static_cast<ParserState*>(parm));
#endif
      }
#line 1871 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 8:
#line 498 "parser.yxx" /* yacc.c:1646  */
    {
#if !EXPOSE_INT_LITS
        initfg(static_cast<ParserState*>(parm));
#endif
      }
#line 1881 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 11:
#line 510 "parser.yxx" /* yacc.c:1646  */
    {
#if EXPOSE_INT_LITS
        initfg(static_cast<ParserState*>(parm));
#endif
      }
#line 1891 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 12:
#line 516 "parser.yxx" /* yacc.c:1646  */
    {
#if EXPOSE_INT_LITS
        initfg(static_cast<ParserState*>(parm));
#endif
      }
#line 1901 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 33:
#line 570 "parser.yxx" /* yacc.c:1646  */
    {
        ParserState* pp = static_cast<ParserState*>(parm);
        yyassert(pp, !(yyvsp[-4].oSet)() || !(yyvsp[-4].oSet).some()->empty(), "Empty var int domain.");
        bool print = (yyvsp[-1].argVec)->hasAtom("output_var");
        pp->intvarTable.put((yyvsp[-2].sValue), pp->intvars.size());
        if (print) {
          pp->output(std::string((yyvsp[-2].sValue)), new AST::IntVar(pp->intvars.size()));
        }
        bool introduced = (yyvsp[-1].argVec)->hasAtom("var_is_introduced");
        bool looks_introduced = (strncmp((yyvsp[-2].sValue), "X_INTRODUCED_", 13) == 0);
        if ((yyvsp[0].oArg)()) {
          AST::Node* arg = (yyvsp[0].oArg).some();
          if (arg->isInt()) {
            pp->intvars.push_back(varspec((yyvsp[-2].sValue),
              new IntVarSpec(arg->getInt(),print,introduced,looks_introduced)));
          } else if (arg->isIntVar()) {
            pp->intvars.push_back(varspec((yyvsp[-2].sValue),
              new IntVarSpec(Alias(arg->getIntVar()),print,introduced,looks_introduced)));
          } else {
            yyassert(pp, false, "Invalid var int initializer.");
          }
          if (!pp->hadError)
            addDomainConstraint(pp, "set_in",
                                new AST::IntVar(pp->intvars.size()-1), (yyvsp[-4].oSet));
          delete arg;
        } else {
          pp->intvars.push_back(varspec((yyvsp[-2].sValue), new IntVarSpec((yyvsp[-4].oSet),print,introduced,looks_introduced)));
        }
        delete (yyvsp[-1].argVec); free((yyvsp[-2].sValue));
      }
#line 1936 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 34:
#line 601 "parser.yxx" /* yacc.c:1646  */
    {
        ParserState* pp = static_cast<ParserState*>(parm);
        bool print = (yyvsp[-1].argVec)->hasAtom("output_var");
        pp->boolvarTable.put((yyvsp[-2].sValue), pp->boolvars.size());
        if (print) {
          pp->output(std::string((yyvsp[-2].sValue)), new AST::BoolVar(pp->boolvars.size()));
        }
        bool introduced = (yyvsp[-1].argVec)->hasAtom("var_is_introduced");
        bool looks_introduced = (strncmp((yyvsp[-2].sValue), "X_INTRODUCED_", 13) == 0);
        if ((yyvsp[0].oArg)()) {
          AST::Node* arg = (yyvsp[0].oArg).some();
          if (arg->isBool()) {
            pp->boolvars.push_back(varspec((yyvsp[-2].sValue),
              new BoolVarSpec(arg->getBool(),print,introduced,looks_introduced)));            
          } else if (arg->isBoolVar()) {
            pp->boolvars.push_back(varspec((yyvsp[-2].sValue),
              new BoolVarSpec(Alias(arg->getBoolVar()),print,introduced,looks_introduced)));
          } else {
            yyassert(pp, false, "Invalid var bool initializer.");
          }
          if (!pp->hadError)
            addDomainConstraint(pp, "set_in",
                                new AST::BoolVar(pp->boolvars.size()-1), (yyvsp[-4].oSet));
          delete arg;
        } else {
          pp->boolvars.push_back(varspec((yyvsp[-2].sValue), new BoolVarSpec((yyvsp[-4].oSet),print,introduced,looks_introduced)));
        }
        delete (yyvsp[-1].argVec); free((yyvsp[-2].sValue));
      }
#line 1970 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 35:
#line 631 "parser.yxx" /* yacc.c:1646  */
    { ParserState* pp = static_cast<ParserState*>(parm);
        yyassert(pp, false, "Floats not supported.");
        delete (yyvsp[-1].argVec); free((yyvsp[-2].sValue));
      }
#line 1979 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 36:
#line 636 "parser.yxx" /* yacc.c:1646  */
    { 
        ParserState* pp = static_cast<ParserState*>(parm);
        bool print = (yyvsp[-1].argVec)->hasAtom("output_var");
        pp->setvarTable.put((yyvsp[-2].sValue), pp->setvars.size());
        if (print) {
          pp->output(std::string((yyvsp[-2].sValue)), new AST::SetVar(pp->setvars.size()));
        }
        bool introduced = (yyvsp[-1].argVec)->hasAtom("var_is_introduced");
        bool looks_introduced = (strncmp((yyvsp[-2].sValue), "X_INTRODUCED_", 13) == 0);
        if ((yyvsp[0].oArg)()) {
          AST::Node* arg = (yyvsp[0].oArg).some();
          if (arg->isSet()) {
            pp->setvars.push_back(varspec((yyvsp[-2].sValue),
              new SetVarSpec(arg->getSet(),print,introduced,looks_introduced)));            
          } else if (arg->isSetVar()) {
            pp->setvars.push_back(varspec((yyvsp[-2].sValue),
              new SetVarSpec(Alias(arg->getSetVar()),print,introduced,looks_introduced)));
            delete arg;
          } else {
            yyassert(pp, false, "Invalid var set initializer.");
            delete arg;
          }
          if (!pp->hadError)
            addDomainConstraint(pp, "set_subset",
                                new AST::SetVar(pp->setvars.size()-1), (yyvsp[-4].oSet));
        } else {
          pp->setvars.push_back(varspec((yyvsp[-2].sValue), new SetVarSpec((yyvsp[-4].oSet),print,introduced,looks_introduced)));
        }
        delete (yyvsp[-1].argVec); free((yyvsp[-2].sValue));
      }
#line 2014 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 37:
#line 667 "parser.yxx" /* yacc.c:1646  */
    {
        ParserState* pp = static_cast<ParserState*>(parm);
        yyassert(pp, !(yyvsp[-5].oSet)() || !(yyvsp[-5].oSet).some()->empty(), "Empty int domain.");
        yyassert(pp, (yyvsp[0].arg)->isInt(), "Invalid int initializer.");
        int i = -1;
        bool isInt = (yyvsp[0].arg)->isInt(i);
        if ((yyvsp[-5].oSet)() && isInt) {
          AST::SetLit* sl = (yyvsp[-5].oSet).some();
          if (sl->interval) {
            yyassert(pp, i >= sl->min && i <= sl->max, "Empty int domain.");
          } else {
            bool found = false;
            for (unsigned int j=0; j<sl->s.size(); j++)
              if (sl->s[j] == i) {
                found = true;
                break;
              }
            yyassert(pp, found, "Empty int domain.");
          }
        }
        pp->intvals.put((yyvsp[-3].sValue), i);
        delete (yyvsp[-2].argVec); free((yyvsp[-3].sValue));        
      }
#line 2042 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 38:
#line 691 "parser.yxx" /* yacc.c:1646  */
    {
        ParserState* pp = static_cast<ParserState*>(parm);
        yyassert(pp, (yyvsp[0].arg)->isBool(), "Invalid bool initializer.");
        if ((yyvsp[0].arg)->isBool()) {
          pp->boolvals.put((yyvsp[-3].sValue), (yyvsp[0].arg)->getBool());
        }
        delete (yyvsp[-2].argVec); free((yyvsp[-3].sValue));        
      }
#line 2055 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 39:
#line 700 "parser.yxx" /* yacc.c:1646  */
    {
        ParserState* pp = static_cast<ParserState*>(parm);
        yyassert(pp, !(yyvsp[-5].oSet)() || !(yyvsp[-5].oSet).some()->empty(), "Empty set domain.");
        yyassert(pp, (yyvsp[0].arg)->isSet(), "Invalid set initializer.");
        AST::SetLit* set = NULL;
        if ((yyvsp[0].arg)->isSet())
          set = (yyvsp[0].arg)->getSet();
        pp->setvals.put((yyvsp[-3].sValue), *set);
        delete set;
        delete (yyvsp[-2].argVec); free((yyvsp[-3].sValue));        
      }
#line 2071 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 40:
#line 713 "parser.yxx" /* yacc.c:1646  */
    {
        ParserState* pp = static_cast<ParserState*>(parm);
        yyassert(pp, (yyvsp[-10].iValue)==1, "Arrays must start at 1");
        if (!pp->hadError) {
          bool print = (yyvsp[-1].argVec)->hasCall("output_array");
          vector<int> vars((yyvsp[-8].iValue));
          yyassert(pp, !(yyvsp[-4].oSet)() || !(yyvsp[-4].oSet).some()->empty(),
                   "Empty var int domain.");
          if (!pp->hadError) {
            if ((yyvsp[0].oVarSpecVec)()) {
              vector<VarSpec*>* vsv = (yyvsp[0].oVarSpecVec).some();
              yyassert(pp, vsv->size() == static_cast<unsigned int>((yyvsp[-8].iValue)),
                       "Initializer size does not match array dimension");
              if (!pp->hadError) {
                for (int i=0; i<(yyvsp[-8].iValue); i++) {
                  IntVarSpec* ivsv = static_cast<IntVarSpec*>((*vsv)[i]);
                  if (ivsv->alias) {
                    vars[i] = ivsv->i;
                  } else {
                    vars[i] = pp->intvars.size();
                    pp->intvars.push_back(varspec((yyvsp[-2].sValue), ivsv));
                  }
                  if (!pp->hadError && (yyvsp[-4].oSet)()) {
                    Option<AST::SetLit*> opt =
                      Option<AST::SetLit*>::some(new AST::SetLit(*(yyvsp[-4].oSet).some()));                    
                    addDomainConstraint(pp, "set_in",
                                        new AST::IntVar(vars[i]),
                                        opt);
                  }
                }
              }
              delete vsv;
            } else {
              IntVarSpec* ispec = new IntVarSpec((yyvsp[-4].oSet),print,!print,false);
              string arrayname = "["; arrayname += (yyvsp[-2].sValue);
              for (int i=0; i<(yyvsp[-8].iValue)-1; i++) {
                vars[i] = pp->intvars.size();
                pp->intvars.push_back(varspec(arrayname, ispec));
              }          
              vars[(yyvsp[-8].iValue)-1] = pp->intvars.size();
              pp->intvars.push_back(varspec((yyvsp[-2].sValue), ispec));
            }
          }
          if (print) {
            AST::Array* a = new AST::Array();
            a->a.push_back(arrayOutput((yyvsp[-1].argVec)->getCall("output_array")));
            AST::Array* output = new AST::Array();
            for (int i=0; i<(yyvsp[-8].iValue); i++)
              output->a.push_back(new AST::IntVar(vars[i]));
            a->a.push_back(output);
            a->a.push_back(new AST::String(")"));
            pp->output(std::string((yyvsp[-2].sValue)), a);
          }
          pp->intvararrays.put((yyvsp[-2].sValue), vars);
        }
        delete (yyvsp[-1].argVec); free((yyvsp[-2].sValue));
      }
#line 2133 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 41:
#line 772 "parser.yxx" /* yacc.c:1646  */
    {
        ParserState* pp = static_cast<ParserState*>(parm);
        bool print = (yyvsp[-1].argVec)->hasCall("output_array");
        yyassert(pp, (yyvsp[-10].iValue)==1, "Arrays must start at 1");
        if (!pp->hadError) {
          vector<int> vars((yyvsp[-8].iValue));
          if ((yyvsp[0].oVarSpecVec)()) {
            vector<VarSpec*>* vsv = (yyvsp[0].oVarSpecVec).some();
            yyassert(pp, vsv->size() == static_cast<unsigned int>((yyvsp[-8].iValue)),
                     "Initializer size does not match array dimension");
            if (!pp->hadError) {
              for (int i=0; i<(yyvsp[-8].iValue); i++) {
                BoolVarSpec* bvsv = static_cast<BoolVarSpec*>((*vsv)[i]);
                if (bvsv->alias)
                  vars[i] = bvsv->i;
                else {
                  vars[i] = pp->boolvars.size();
                  pp->boolvars.push_back(varspec((yyvsp[-2].sValue), (*vsv)[i]));
                }
                if (!pp->hadError && (yyvsp[-4].oSet)()) {
                  Option<AST::SetLit*> opt =
                    Option<AST::SetLit*>::some(new AST::SetLit(*(yyvsp[-4].oSet).some()));                    
                  addDomainConstraint(pp, "set_in",
                                      new AST::BoolVar(vars[i]),
                                      opt);
                }
              }
            }
            delete vsv;
          } else {
            for (int i=0; i<(yyvsp[-8].iValue); i++) {
              vars[i] = pp->boolvars.size();
              pp->boolvars.push_back(varspec((yyvsp[-2].sValue),
                                             new BoolVarSpec((yyvsp[-4].oSet),print,!print,false)));
            }          
          }
          if (print) {
            AST::Array* a = new AST::Array();
            a->a.push_back(arrayOutput((yyvsp[-1].argVec)->getCall("output_array")));
            AST::Array* output = new AST::Array();
            for (int i=0; i<(yyvsp[-8].iValue); i++)
              output->a.push_back(new AST::BoolVar(vars[i]));
            a->a.push_back(output);
            a->a.push_back(new AST::String(")"));
            pp->output(std::string((yyvsp[-2].sValue)), a);
          }
          pp->boolvararrays.put((yyvsp[-2].sValue), vars);
        }
        delete (yyvsp[-1].argVec); free((yyvsp[-2].sValue));
      }
#line 2188 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 42:
#line 824 "parser.yxx" /* yacc.c:1646  */
    { 
        ParserState* pp = static_cast<ParserState*>(parm);
        yyassert(pp, false, "Floats not supported.");
        delete (yyvsp[-1].argVec); free((yyvsp[-2].sValue));
      }
#line 2198 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 43:
#line 831 "parser.yxx" /* yacc.c:1646  */
    { 
        ParserState* pp = static_cast<ParserState*>(parm);
        bool print = (yyvsp[-1].argVec)->hasCall("output_array");
        yyassert(pp, (yyvsp[-12].iValue)==1, "Arrays must start at 1");
        if (!pp->hadError) {
          vector<int> vars((yyvsp[-10].iValue));
          if ((yyvsp[0].oVarSpecVec)()) {
            vector<VarSpec*>* vsv = (yyvsp[0].oVarSpecVec).some();
            yyassert(pp, vsv->size() == static_cast<unsigned int>((yyvsp[-10].iValue)),
                     "Initializer size does not match array dimension");
            if (!pp->hadError) {
              for (int i=0; i<(yyvsp[-10].iValue); i++) {
                SetVarSpec* svsv = static_cast<SetVarSpec*>((*vsv)[i]);
                if (svsv->alias)
                  vars[i] = svsv->i;
                else {
                  vars[i] = pp->setvars.size();
                  pp->setvars.push_back(varspec((yyvsp[-2].sValue), (*vsv)[i]));
                }
                if (!pp->hadError && (yyvsp[-4].oSet)()) {
                  Option<AST::SetLit*> opt =
                    Option<AST::SetLit*>::some(new AST::SetLit(*(yyvsp[-4].oSet).some()));                    
                  addDomainConstraint(pp, "set_subset",
                                      new AST::SetVar(vars[i]),
                                      opt);
                }
              }
            }
            delete vsv;
          } else {
            SetVarSpec* ispec = new SetVarSpec((yyvsp[-4].oSet),print,!print, false);
            string arrayname = "["; arrayname += (yyvsp[-2].sValue);
            for (int i=0; i<(yyvsp[-10].iValue)-1; i++) {
              vars[i] = pp->setvars.size();
              pp->setvars.push_back(varspec(arrayname, ispec));
            }          
            vars[(yyvsp[-10].iValue)-1] = pp->setvars.size();
            pp->setvars.push_back(varspec((yyvsp[-2].sValue), ispec));
          }
          if (print) {
            AST::Array* a = new AST::Array();
            a->a.push_back(arrayOutput((yyvsp[-1].argVec)->getCall("output_array")));
            AST::Array* output = new AST::Array();
            for (int i=0; i<(yyvsp[-10].iValue); i++)
              output->a.push_back(new AST::SetVar(vars[i]));
            a->a.push_back(output);
            a->a.push_back(new AST::String(")"));
            pp->output(std::string((yyvsp[-2].sValue)), a);
          }
          pp->setvararrays.put((yyvsp[-2].sValue), vars);
        }
        delete (yyvsp[-1].argVec); free((yyvsp[-2].sValue));
      }
#line 2256 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 44:
#line 886 "parser.yxx" /* yacc.c:1646  */
    {
        ParserState* pp = static_cast<ParserState*>(parm);
        yyassert(pp, (yyvsp[-12].iValue)==1, "Arrays must start at 1");
        yyassert(pp, (yyvsp[-1].setValue)->size() == static_cast<unsigned int>((yyvsp[-10].iValue)),
                 "Initializer size does not match array dimension");
        if (!pp->hadError)
          pp->intvalarrays.put((yyvsp[-5].sValue), *(yyvsp[-1].setValue));
        delete (yyvsp[-1].setValue);
        free((yyvsp[-5].sValue));
        delete (yyvsp[-4].argVec);
      }
#line 2272 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 45:
#line 899 "parser.yxx" /* yacc.c:1646  */
    {
        ParserState* pp = static_cast<ParserState*>(parm);
        yyassert(pp, (yyvsp[-12].iValue)==1, "Arrays must start at 1");
        yyassert(pp, (yyvsp[-1].setValue)->size() == static_cast<unsigned int>((yyvsp[-10].iValue)),
                 "Initializer size does not match array dimension");
        if (!pp->hadError)
          pp->boolvalarrays.put((yyvsp[-5].sValue), *(yyvsp[-1].setValue));
        delete (yyvsp[-1].setValue);
        free((yyvsp[-5].sValue));
        delete (yyvsp[-4].argVec);
      }
#line 2288 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 46:
#line 912 "parser.yxx" /* yacc.c:1646  */
    {
        ParserState* pp = static_cast<ParserState*>(parm);
        yyassert(pp, false, "Floats not supported.");
        delete (yyvsp[-4].argVec); free((yyvsp[-5].sValue));
      }
#line 2298 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 47:
#line 919 "parser.yxx" /* yacc.c:1646  */
    {
        ParserState* pp = static_cast<ParserState*>(parm);
        yyassert(pp, (yyvsp[-14].iValue)==1, "Arrays must start at 1");
        yyassert(pp, (yyvsp[-1].setValueList)->size() == static_cast<unsigned int>((yyvsp[-12].iValue)),
                 "Initializer size does not match array dimension");
        if (!pp->hadError)
          pp->setvalarrays.put((yyvsp[-5].sValue), *(yyvsp[-1].setValueList));
        delete (yyvsp[-1].setValueList);
        delete (yyvsp[-4].argVec); free((yyvsp[-5].sValue));
      }
#line 2313 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 48:
#line 932 "parser.yxx" /* yacc.c:1646  */
    { 
        (yyval.varSpec) = new IntVarSpec((yyvsp[0].iValue),false,true,false);
      }
#line 2321 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 49:
#line 936 "parser.yxx" /* yacc.c:1646  */
    { 
        int v = 0;
        ParserState* pp = static_cast<ParserState*>(parm);
        if (pp->intvarTable.get((yyvsp[0].sValue), v))
          (yyval.varSpec) = new IntVarSpec(Alias(v),false,true,false);
        else {
          pp->err << "Error: undefined identifier " << (yyvsp[0].sValue)
                  << " in line no. "
                  << yyget_lineno(pp->yyscanner) << std::endl;
          pp->hadError = true;
          (yyval.varSpec) = new IntVarSpec(0,false,true,false); // keep things consistent
        }
        free((yyvsp[0].sValue));
      }
#line 2340 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 50:
#line 951 "parser.yxx" /* yacc.c:1646  */
    { 
        vector<int> v;
        ParserState* pp = static_cast<ParserState*>(parm);
        if (pp->intvararrays.get((yyvsp[-3].sValue), v)) {
          yyassert(pp,static_cast<unsigned int>((yyvsp[-1].iValue)) > 0 && 
                      static_cast<unsigned int>((yyvsp[-1].iValue)) <= v.size(),
                   "array access out of bounds");
          if (!pp->hadError)
            (yyval.varSpec) = new IntVarSpec(Alias(v[(yyvsp[-1].iValue)-1]),false,true,false);
          else
            (yyval.varSpec) = new IntVarSpec(0,false,true,false); // keep things consistent
        } else {
          pp->err << "Error: undefined array identifier " << (yyvsp[-3].sValue)
                  << " in line no. "
                  << yyget_lineno(pp->yyscanner) << std::endl;
          pp->hadError = true;
          (yyval.varSpec) = new IntVarSpec(0,false,true,false); // keep things consistent
        }
        free((yyvsp[-3].sValue));
      }
#line 2365 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 51:
#line 974 "parser.yxx" /* yacc.c:1646  */
    { (yyval.varSpecVec) = new vector<VarSpec*>(0); }
#line 2371 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 52:
#line 976 "parser.yxx" /* yacc.c:1646  */
    { (yyval.varSpecVec) = (yyvsp[-1].varSpecVec); }
#line 2377 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 53:
#line 980 "parser.yxx" /* yacc.c:1646  */
    { (yyval.varSpecVec) = new vector<VarSpec*>(1); (*(yyval.varSpecVec))[0] = (yyvsp[0].varSpec); }
#line 2383 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 54:
#line 982 "parser.yxx" /* yacc.c:1646  */
    { (yyval.varSpecVec) = (yyvsp[-2].varSpecVec); (yyval.varSpecVec)->push_back((yyvsp[0].varSpec)); }
#line 2389 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 57:
#line 987 "parser.yxx" /* yacc.c:1646  */
    { (yyval.varSpecVec) = (yyvsp[-1].varSpecVec); }
#line 2395 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 58:
#line 991 "parser.yxx" /* yacc.c:1646  */
    { (yyval.varSpec) = new FloatVarSpec((yyvsp[0].dValue),false,true,false); }
#line 2401 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 59:
#line 993 "parser.yxx" /* yacc.c:1646  */
    { 
        int v = 0;
        ParserState* pp = static_cast<ParserState*>(parm);
        if (pp->floatvarTable.get((yyvsp[0].sValue), v))
          (yyval.varSpec) = new FloatVarSpec(Alias(v),false,true,false);
        else {
          pp->err << "Error: undefined identifier " << (yyvsp[0].sValue)
                  << " in line no. "
                  << yyget_lineno(pp->yyscanner) << std::endl;
          pp->hadError = true;
          (yyval.varSpec) = new FloatVarSpec(0.0,false,true,false);
        }
        free((yyvsp[0].sValue));
      }
#line 2420 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 60:
#line 1008 "parser.yxx" /* yacc.c:1646  */
    { 
        vector<int> v;
        ParserState* pp = static_cast<ParserState*>(parm);
        if (pp->floatvararrays.get((yyvsp[-3].sValue), v)) {
          yyassert(pp,static_cast<unsigned int>((yyvsp[-1].iValue)) > 0 && 
                      static_cast<unsigned int>((yyvsp[-1].iValue)) <= v.size(),
                   "array access out of bounds");
          if (!pp->hadError)
            (yyval.varSpec) = new FloatVarSpec(Alias(v[(yyvsp[-1].iValue)-1]),false,true,false);
          else
            (yyval.varSpec) = new FloatVarSpec(0.0,false,true,false);
        } else {
          pp->err << "Error: undefined array identifier " << (yyvsp[-3].sValue)
                  << " in line no. "
                  << yyget_lineno(pp->yyscanner) << std::endl;
          pp->hadError = true;
          (yyval.varSpec) = new FloatVarSpec(0.0,false,true,false);
        }
        free((yyvsp[-3].sValue));
      }
#line 2445 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 61:
#line 1031 "parser.yxx" /* yacc.c:1646  */
    { (yyval.varSpecVec) = new vector<VarSpec*>(0); }
#line 2451 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 62:
#line 1033 "parser.yxx" /* yacc.c:1646  */
    { (yyval.varSpecVec) = (yyvsp[-1].varSpecVec); }
#line 2457 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 63:
#line 1037 "parser.yxx" /* yacc.c:1646  */
    { (yyval.varSpecVec) = new vector<VarSpec*>(1); (*(yyval.varSpecVec))[0] = (yyvsp[0].varSpec); }
#line 2463 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 64:
#line 1039 "parser.yxx" /* yacc.c:1646  */
    { (yyval.varSpecVec) = (yyvsp[-2].varSpecVec); (yyval.varSpecVec)->push_back((yyvsp[0].varSpec)); }
#line 2469 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 65:
#line 1043 "parser.yxx" /* yacc.c:1646  */
    { (yyval.varSpecVec) = (yyvsp[-1].varSpecVec); }
#line 2475 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 66:
#line 1047 "parser.yxx" /* yacc.c:1646  */
    { (yyval.varSpec) = new BoolVarSpec((yyvsp[0].iValue),false,true,false); }
#line 2481 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 67:
#line 1049 "parser.yxx" /* yacc.c:1646  */
    { 
        int v = 0;
        ParserState* pp = static_cast<ParserState*>(parm);
        if (pp->boolvarTable.get((yyvsp[0].sValue), v))
          (yyval.varSpec) = new BoolVarSpec(Alias(v),false,true,false);
        else {
          pp->err << "Error: undefined identifier " << (yyvsp[0].sValue)
                  << " in line no. "
                  << yyget_lineno(pp->yyscanner) << std::endl;
          pp->hadError = true;
          (yyval.varSpec) = new BoolVarSpec(false,false,true,false);
        }
        free((yyvsp[0].sValue));
      }
#line 2500 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 68:
#line 1064 "parser.yxx" /* yacc.c:1646  */
    { 
        vector<int> v;
        ParserState* pp = static_cast<ParserState*>(parm);
        if (pp->boolvararrays.get((yyvsp[-3].sValue), v)) {
          yyassert(pp,static_cast<unsigned int>((yyvsp[-1].iValue)) > 0 && 
                      static_cast<unsigned int>((yyvsp[-1].iValue)) <= v.size(),
                   "array access out of bounds");
          if (!pp->hadError)
            (yyval.varSpec) = new BoolVarSpec(Alias(v[(yyvsp[-1].iValue)-1]),false,true,false);
          else
            (yyval.varSpec) = new BoolVarSpec(false,false,true,false);
        } else {
          pp->err << "Error: undefined array identifier " << (yyvsp[-3].sValue)
                  << " in line no. "
                  << yyget_lineno(pp->yyscanner) << std::endl;
          pp->hadError = true;
          (yyval.varSpec) = new BoolVarSpec(false,false,true,false);
        }
        free((yyvsp[-3].sValue));
      }
#line 2525 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 69:
#line 1087 "parser.yxx" /* yacc.c:1646  */
    { (yyval.varSpecVec) = new vector<VarSpec*>(0); }
#line 2531 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 70:
#line 1089 "parser.yxx" /* yacc.c:1646  */
    { (yyval.varSpecVec) = (yyvsp[-1].varSpecVec); }
#line 2537 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 71:
#line 1093 "parser.yxx" /* yacc.c:1646  */
    { (yyval.varSpecVec) = new vector<VarSpec*>(1); (*(yyval.varSpecVec))[0] = (yyvsp[0].varSpec); }
#line 2543 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 72:
#line 1095 "parser.yxx" /* yacc.c:1646  */
    { (yyval.varSpecVec) = (yyvsp[-2].varSpecVec); (yyval.varSpecVec)->push_back((yyvsp[0].varSpec)); }
#line 2549 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 73:
#line 1097 "parser.yxx" /* yacc.c:1646  */
    { (yyval.varSpecVec) = (yyvsp[-1].varSpecVec); }
#line 2555 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 74:
#line 1101 "parser.yxx" /* yacc.c:1646  */
    { (yyval.varSpec) = new SetVarSpec(Option<AST::SetLit*>::some((yyvsp[0].setLit)),false,true,false); }
#line 2561 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 75:
#line 1103 "parser.yxx" /* yacc.c:1646  */
    { 
        ParserState* pp = static_cast<ParserState*>(parm);
        int v = 0;
        if (pp->setvarTable.get((yyvsp[0].sValue), v))
          (yyval.varSpec) = new SetVarSpec(Alias(v),false,true,false);
        else {
          pp->err << "Error: undefined identifier " << (yyvsp[0].sValue)
                  << " in line no. "
                  << yyget_lineno(pp->yyscanner) << std::endl;
          pp->hadError = true;
          (yyval.varSpec) = new SetVarSpec(Alias(0),false,true,false);
        }
        free((yyvsp[0].sValue));
      }
#line 2580 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 76:
#line 1118 "parser.yxx" /* yacc.c:1646  */
    { 
        vector<int> v;
        ParserState* pp = static_cast<ParserState*>(parm);
        if (pp->setvararrays.get((yyvsp[-3].sValue), v)) {
          yyassert(pp,static_cast<unsigned int>((yyvsp[-1].iValue)) > 0 && 
                      static_cast<unsigned int>((yyvsp[-1].iValue)) <= v.size(),
                   "array access out of bounds");
          if (!pp->hadError)
            (yyval.varSpec) = new SetVarSpec(Alias(v[(yyvsp[-1].iValue)-1]),false,true,false);
          else
            (yyval.varSpec) = new SetVarSpec(Alias(0),false,true,false);
        } else {
          pp->err << "Error: undefined array identifier " << (yyvsp[-3].sValue)
                  << " in line no. "
                  << yyget_lineno(pp->yyscanner) << std::endl;
          pp->hadError = true;
          (yyval.varSpec) = new SetVarSpec(Alias(0),false,true,false);
        }
        free((yyvsp[-3].sValue));
      }
#line 2605 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 77:
#line 1141 "parser.yxx" /* yacc.c:1646  */
    { (yyval.varSpecVec) = new vector<VarSpec*>(0); }
#line 2611 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 78:
#line 1143 "parser.yxx" /* yacc.c:1646  */
    { (yyval.varSpecVec) = (yyvsp[-1].varSpecVec); }
#line 2617 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 79:
#line 1147 "parser.yxx" /* yacc.c:1646  */
    { (yyval.varSpecVec) = new vector<VarSpec*>(1); (*(yyval.varSpecVec))[0] = (yyvsp[0].varSpec); }
#line 2623 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 80:
#line 1149 "parser.yxx" /* yacc.c:1646  */
    { (yyval.varSpecVec) = (yyvsp[-2].varSpecVec); (yyval.varSpecVec)->push_back((yyvsp[0].varSpec)); }
#line 2629 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 81:
#line 1152 "parser.yxx" /* yacc.c:1646  */
    { (yyval.varSpecVec) = (yyvsp[-1].varSpecVec); }
#line 2635 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 82:
#line 1156 "parser.yxx" /* yacc.c:1646  */
    { (yyval.oVarSpecVec) = Option<vector<VarSpec*>* >::none(); }
#line 2641 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 83:
#line 1158 "parser.yxx" /* yacc.c:1646  */
    { (yyval.oVarSpecVec) = Option<vector<VarSpec*>* >::some((yyvsp[0].varSpecVec)); }
#line 2647 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 84:
#line 1162 "parser.yxx" /* yacc.c:1646  */
    { (yyval.oVarSpecVec) = Option<vector<VarSpec*>* >::none(); }
#line 2653 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 85:
#line 1164 "parser.yxx" /* yacc.c:1646  */
    { (yyval.oVarSpecVec) = Option<vector<VarSpec*>* >::some((yyvsp[0].varSpecVec)); }
#line 2659 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 86:
#line 1168 "parser.yxx" /* yacc.c:1646  */
    { (yyval.oVarSpecVec) = Option<vector<VarSpec*>* >::none(); }
#line 2665 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 87:
#line 1170 "parser.yxx" /* yacc.c:1646  */
    { (yyval.oVarSpecVec) = Option<vector<VarSpec*>* >::some((yyvsp[0].varSpecVec)); }
#line 2671 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 88:
#line 1174 "parser.yxx" /* yacc.c:1646  */
    { (yyval.oVarSpecVec) = Option<vector<VarSpec*>* >::none(); }
#line 2677 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 89:
#line 1176 "parser.yxx" /* yacc.c:1646  */
    { (yyval.oVarSpecVec) = Option<vector<VarSpec*>* >::some((yyvsp[0].varSpecVec)); }
#line 2683 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 90:
#line 1180 "parser.yxx" /* yacc.c:1646  */
    { 
        ParserState *pp = static_cast<ParserState*>(parm);
#if EXPOSE_INT_LITS
        pp->domainConstraints2.push_back(std::pair<ConExpr*, AST::Node*>(new ConExpr((yyvsp[-4].sValue), (yyvsp[-2].argVec)), (yyvsp[0].argVec)));
#else
        ConExpr c((yyvsp[-4].sValue), (yyvsp[-2].argVec));
        if (!pp->hadError) {
          try {
            pp->fg->postConstraint(c, (yyvsp[0].argVec));
          } catch (FlatZinc::Error& e) {
            yyerror(pp, e.toString().c_str());
          }
        }
        delete (yyvsp[0].argVec);
#endif
        free((yyvsp[-4].sValue));
      }
#line 2705 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 91:
#line 1198 "parser.yxx" /* yacc.c:1646  */
    {
        ParserState *pp = static_cast<ParserState*>(parm);
        AST::Array* args = new AST::Array(2);
        args->a[0] = getVarRefArg(pp,(yyvsp[-1].sValue));
        args->a[1] = new AST::BoolLit(true);
#if EXPOSE_INT_LITS
        pp->domainConstraints2.push_back(std::pair<ConExpr*, AST::Node*>(new ConExpr("bool_eq", args), (yyvsp[0].argVec)));
#else
        ConExpr c("bool_eq", args);
        if (!pp->hadError) {
          try {
            pp->fg->postConstraint(c, (yyvsp[0].argVec));
          } catch (FlatZinc::Error& e) {
            yyerror(pp, e.toString().c_str());
          }
        }
        delete (yyvsp[0].argVec);
#endif
        free((yyvsp[-1].sValue));
      }
#line 2730 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 92:
#line 1219 "parser.yxx" /* yacc.c:1646  */
    { 
          ParserState *pp = static_cast<ParserState*>(parm);
          AST::Array* args = new AST::Array(2);
          args->a[0] = getArrayElement(pp,(yyvsp[-4].sValue),(yyvsp[-2].iValue));
          args->a[1] = new AST::BoolLit(true);
#if EXPOSE_INT_LITS
          pp->domainConstraints2.push_back(std::pair<ConExpr*, AST::Node*>(new ConExpr("bool_eq", args), (yyvsp[0].argVec)));
#else
          ConExpr c("bool_eq", args);
          if (!pp->hadError) {
            try {
              pp->fg->postConstraint(c, (yyvsp[0].argVec));
            } catch (FlatZinc::Error& e) {
              yyerror(pp, e.toString().c_str());
            }
          }
          delete (yyvsp[0].argVec);
#endif
          free((yyvsp[-4].sValue));
        }
#line 2755 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 93:
#line 1241 "parser.yxx" /* yacc.c:1646  */
    { 
        ParserState *pp = static_cast<ParserState*>(parm);
        if (!pp->hadError) {
          pp->fg->solve((yyvsp[-1].argVec));
        }
        delete (yyvsp[-1].argVec);
      }
#line 2767 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 94:
#line 1249 "parser.yxx" /* yacc.c:1646  */
    { 
        ParserState *pp = static_cast<ParserState*>(parm);
        if (!pp->hadError) {
          if ((yyvsp[-1].bValue))
            pp->fg->minimize((yyvsp[0].iValue),(yyvsp[-2].argVec));
          else
            pp->fg->maximize((yyvsp[0].iValue),(yyvsp[-2].argVec));
        }
        delete (yyvsp[-2].argVec);
      }
#line 2782 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 95:
#line 1266 "parser.yxx" /* yacc.c:1646  */
    { (yyval.oSet) = Option<AST::SetLit* >::none(); }
#line 2788 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 96:
#line 1268 "parser.yxx" /* yacc.c:1646  */
    { (yyval.oSet) = Option<AST::SetLit* >::some(new AST::SetLit(*(yyvsp[-1].setValue))); }
#line 2794 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 97:
#line 1270 "parser.yxx" /* yacc.c:1646  */
    { 
        (yyval.oSet) = Option<AST::SetLit* >::some(new AST::SetLit((yyvsp[-2].iValue), (yyvsp[0].iValue)));
      }
#line 2802 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 98:
#line 1276 "parser.yxx" /* yacc.c:1646  */
    { (yyval.oSet) = Option<AST::SetLit* >::none(); }
#line 2808 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 99:
#line 1278 "parser.yxx" /* yacc.c:1646  */
    { bool haveTrue = false;
        bool haveFalse = false;
        for (int i=(yyvsp[-2].setValue)->size(); i--;) {
          haveTrue |= ((*(yyvsp[-2].setValue))[i] == 1);
          haveFalse |= ((*(yyvsp[-2].setValue))[i] == 0);
        }
        delete (yyvsp[-2].setValue);
        (yyval.oSet) = Option<AST::SetLit* >::some(
          new AST::SetLit(!haveFalse,haveTrue));
      }
#line 2823 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 102:
#line 1299 "parser.yxx" /* yacc.c:1646  */
    { (yyval.setLit) = new AST::SetLit(*(yyvsp[-1].setValue)); }
#line 2829 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 103:
#line 1301 "parser.yxx" /* yacc.c:1646  */
    { (yyval.setLit) = new AST::SetLit((yyvsp[-2].iValue), (yyvsp[0].iValue)); }
#line 2835 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 104:
#line 1307 "parser.yxx" /* yacc.c:1646  */
    { (yyval.setValue) = new vector<int>(0); }
#line 2841 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 105:
#line 1309 "parser.yxx" /* yacc.c:1646  */
    { (yyval.setValue) = (yyvsp[-1].setValue); }
#line 2847 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 106:
#line 1313 "parser.yxx" /* yacc.c:1646  */
    { (yyval.setValue) = new vector<int>(1); (*(yyval.setValue))[0] = (yyvsp[0].iValue); }
#line 2853 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 107:
#line 1315 "parser.yxx" /* yacc.c:1646  */
    { (yyval.setValue) = (yyvsp[-2].setValue); (yyval.setValue)->push_back((yyvsp[0].iValue)); }
#line 2859 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 108:
#line 1319 "parser.yxx" /* yacc.c:1646  */
    { (yyval.setValue) = new vector<int>(0); }
#line 2865 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 109:
#line 1321 "parser.yxx" /* yacc.c:1646  */
    { (yyval.setValue) = (yyvsp[-1].setValue); }
#line 2871 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 110:
#line 1325 "parser.yxx" /* yacc.c:1646  */
    { (yyval.setValue) = new vector<int>(1); (*(yyval.setValue))[0] = (yyvsp[0].iValue); }
#line 2877 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 111:
#line 1327 "parser.yxx" /* yacc.c:1646  */
    { (yyval.setValue) = (yyvsp[-2].setValue); (yyval.setValue)->push_back((yyvsp[0].iValue)); }
#line 2883 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 112:
#line 1331 "parser.yxx" /* yacc.c:1646  */
    { (yyval.floatSetValue) = new vector<double>(0); }
#line 2889 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 113:
#line 1333 "parser.yxx" /* yacc.c:1646  */
    { (yyval.floatSetValue) = (yyvsp[-1].floatSetValue); }
#line 2895 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 114:
#line 1337 "parser.yxx" /* yacc.c:1646  */
    { (yyval.floatSetValue) = new vector<double>(1); (*(yyval.floatSetValue))[0] = (yyvsp[0].dValue); }
#line 2901 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 115:
#line 1339 "parser.yxx" /* yacc.c:1646  */
    { (yyval.floatSetValue) = (yyvsp[-2].floatSetValue); (yyval.floatSetValue)->push_back((yyvsp[0].dValue)); }
#line 2907 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 116:
#line 1343 "parser.yxx" /* yacc.c:1646  */
    { (yyval.setValueList) = new vector<AST::SetLit>(0); }
#line 2913 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 117:
#line 1345 "parser.yxx" /* yacc.c:1646  */
    { (yyval.setValueList) = (yyvsp[-1].setValueList); }
#line 2919 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 118:
#line 1349 "parser.yxx" /* yacc.c:1646  */
    { (yyval.setValueList) = new vector<AST::SetLit>(1); (*(yyval.setValueList))[0] = *(yyvsp[0].setLit); delete (yyvsp[0].setLit); }
#line 2925 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 119:
#line 1351 "parser.yxx" /* yacc.c:1646  */
    { (yyval.setValueList) = (yyvsp[-2].setValueList); (yyval.setValueList)->push_back(*(yyvsp[0].setLit)); delete (yyvsp[0].setLit); }
#line 2931 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 120:
#line 1359 "parser.yxx" /* yacc.c:1646  */
    { (yyval.argVec) = new AST::Array((yyvsp[0].arg)); }
#line 2937 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 121:
#line 1361 "parser.yxx" /* yacc.c:1646  */
    { (yyval.argVec) = (yyvsp[-2].argVec); (yyval.argVec)->append((yyvsp[0].arg)); }
#line 2943 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 122:
#line 1365 "parser.yxx" /* yacc.c:1646  */
    { (yyval.arg) = (yyvsp[0].arg); }
#line 2949 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 123:
#line 1367 "parser.yxx" /* yacc.c:1646  */
    { (yyval.arg) = (yyvsp[-1].argVec); }
#line 2955 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 124:
#line 1371 "parser.yxx" /* yacc.c:1646  */
    { (yyval.oArg) = Option<AST::Node*>::none(); }
#line 2961 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 125:
#line 1373 "parser.yxx" /* yacc.c:1646  */
    { (yyval.oArg) = Option<AST::Node*>::some((yyvsp[0].arg)); }
#line 2967 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 126:
#line 1377 "parser.yxx" /* yacc.c:1646  */
    { (yyval.arg) = new AST::BoolLit((yyvsp[0].iValue)); }
#line 2973 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 127:
#line 1379 "parser.yxx" /* yacc.c:1646  */
    { (yyval.arg) = new AST::IntLit((yyvsp[0].iValue)); }
#line 2979 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 128:
#line 1381 "parser.yxx" /* yacc.c:1646  */
    { (yyval.arg) = new AST::FloatLit((yyvsp[0].dValue)); }
#line 2985 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 129:
#line 1383 "parser.yxx" /* yacc.c:1646  */
    { (yyval.arg) = (yyvsp[0].setLit); }
#line 2991 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 130:
#line 1385 "parser.yxx" /* yacc.c:1646  */
    { 
        vector<int> as;
        ParserState* pp = static_cast<ParserState*>(parm);
        if (pp->intvararrays.get((yyvsp[0].sValue), as)) {
          AST::Array *ia = new AST::Array(as.size());
          for (int i=as.size(); i--;)
            ia->a[i] = new AST::IntVar(as[i]);
          (yyval.arg) = ia;
        } else if (pp->boolvararrays.get((yyvsp[0].sValue), as)) {
          AST::Array *ia = new AST::Array(as.size());
          for (int i=as.size(); i--;)
            ia->a[i] = new AST::BoolVar(as[i]);
          (yyval.arg) = ia;
        } else if (pp->setvararrays.get((yyvsp[0].sValue), as)) {
          AST::Array *ia = new AST::Array(as.size());
          for (int i=as.size(); i--;)
            ia->a[i] = new AST::SetVar(as[i]);
          (yyval.arg) = ia;
        } else {
          std::vector<int> is;
          std::vector<AST::SetLit> isS;
          int ival = 0;
          bool bval = false;
          if (pp->intvalarrays.get((yyvsp[0].sValue), is)) {
            AST::Array *v = new AST::Array(is.size());
            for (int i=is.size(); i--;)
              v->a[i] = new AST::IntLit(is[i]);
            (yyval.arg) = v;
          } else if (pp->boolvalarrays.get((yyvsp[0].sValue), is)) {
            AST::Array *v = new AST::Array(is.size());
            for (int i=is.size(); i--;)
              v->a[i] = new AST::BoolLit(is[i]);
            (yyval.arg) = v;
          } else if (pp->setvalarrays.get((yyvsp[0].sValue), isS)) {
            AST::Array *v = new AST::Array(isS.size());
            for (int i=isS.size(); i--;)
              v->a[i] = new AST::SetLit(isS[i]);
            (yyval.arg) = v;            
          } else if (pp->intvals.get((yyvsp[0].sValue), ival)) {
            (yyval.arg) = new AST::IntLit(ival);
          } else if (pp->boolvals.get((yyvsp[0].sValue), bval)) {
            (yyval.arg) = new AST::BoolLit(bval);
          } else {
            (yyval.arg) = getVarRefArg(pp,(yyvsp[0].sValue));
          }
        }
        free((yyvsp[0].sValue));
      }
#line 3044 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 131:
#line 1434 "parser.yxx" /* yacc.c:1646  */
    { 
        ParserState* pp = static_cast<ParserState*>(parm);
        int i = -1;
        yyassert(pp, (yyvsp[-1].arg)->isInt(i), "Non-integer array index.");
        if (!pp->hadError)
          (yyval.arg) = getArrayElement(static_cast<ParserState*>(parm),(yyvsp[-3].sValue),i);
        else
          (yyval.arg) = new AST::IntLit(0); // keep things consistent
        free((yyvsp[-3].sValue));
      }
#line 3059 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 132:
#line 1447 "parser.yxx" /* yacc.c:1646  */
    { (yyval.argVec) = new AST::Array(0); }
#line 3065 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 133:
#line 1449 "parser.yxx" /* yacc.c:1646  */
    { (yyval.argVec) = (yyvsp[-1].argVec); }
#line 3071 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 134:
#line 1453 "parser.yxx" /* yacc.c:1646  */
    { (yyval.argVec) = new AST::Array((yyvsp[0].arg)); }
#line 3077 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 135:
#line 1455 "parser.yxx" /* yacc.c:1646  */
    { (yyval.argVec) = (yyvsp[-2].argVec); (yyval.argVec)->append((yyvsp[0].arg)); }
#line 3083 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 136:
#line 1463 "parser.yxx" /* yacc.c:1646  */
    { 
        ParserState *pp = static_cast<ParserState*>(parm);
        if (!pp->intvarTable.get((yyvsp[0].sValue), (yyval.iValue))) {
          pp->err << "Error: unknown integer variable " << (yyvsp[0].sValue)
                  << " in line no. "
                  << yyget_lineno(pp->yyscanner) << std::endl;
          pp->hadError = true;
        }
        free((yyvsp[0].sValue));
      }
#line 3098 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 137:
#line 1474 "parser.yxx" /* yacc.c:1646  */
    {
        vector<int> tmp;
        ParserState *pp = static_cast<ParserState*>(parm);
        if (!pp->intvararrays.get((yyvsp[-3].sValue), tmp)) {
          pp->err << "Error: unknown integer variable array " << (yyvsp[-3].sValue)
                  << " in line no. "
                  << yyget_lineno(pp->yyscanner) << std::endl;
          pp->hadError = true;
        }
        if ((yyvsp[-1].iValue) == 0 || static_cast<unsigned int>((yyvsp[-1].iValue)) > tmp.size()) {
          pp->err << "Error: array index out of bounds for array " << (yyvsp[-3].sValue)
                  << " in line no. "
                  << yyget_lineno(pp->yyscanner) << std::endl;
          pp->hadError = true;
        } else {
          (yyval.iValue) = tmp[(yyvsp[-1].iValue)-1];
        }
        free((yyvsp[-3].sValue));
      }
#line 3122 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 140:
#line 1504 "parser.yxx" /* yacc.c:1646  */
    { (yyval.argVec) = NULL; }
#line 3128 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 141:
#line 1506 "parser.yxx" /* yacc.c:1646  */
    { (yyval.argVec) = (yyvsp[0].argVec); }
#line 3134 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 142:
#line 1510 "parser.yxx" /* yacc.c:1646  */
    { (yyval.argVec) = new AST::Array((yyvsp[0].arg)); }
#line 3140 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 143:
#line 1512 "parser.yxx" /* yacc.c:1646  */
    { (yyval.argVec) = (yyvsp[-2].argVec); (yyval.argVec)->append((yyvsp[0].arg)); }
#line 3146 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 144:
#line 1516 "parser.yxx" /* yacc.c:1646  */
    { 
        (yyval.arg) = new AST::Call((yyvsp[-3].sValue), AST::extractSingleton((yyvsp[-1].arg))); free((yyvsp[-3].sValue));
      }
#line 3154 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 145:
#line 1520 "parser.yxx" /* yacc.c:1646  */
    { (yyval.arg) = (yyvsp[0].arg); }
#line 3160 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 146:
#line 1524 "parser.yxx" /* yacc.c:1646  */
    { (yyval.arg) = new AST::Array((yyvsp[0].arg)); }
#line 3166 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 147:
#line 1526 "parser.yxx" /* yacc.c:1646  */
    { (yyval.arg) = (yyvsp[-2].arg); (yyval.arg)->append((yyvsp[0].arg)); }
#line 3172 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 148:
#line 1530 "parser.yxx" /* yacc.c:1646  */
    { (yyval.arg) = (yyvsp[0].arg); }
#line 3178 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 149:
#line 1532 "parser.yxx" /* yacc.c:1646  */
    { (yyval.arg) = (yyvsp[-1].arg); }
#line 3184 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 150:
#line 1536 "parser.yxx" /* yacc.c:1646  */
    { (yyval.arg) = new AST::BoolLit((yyvsp[0].iValue)); }
#line 3190 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 151:
#line 1538 "parser.yxx" /* yacc.c:1646  */
    { (yyval.arg) = new AST::IntLit((yyvsp[0].iValue)); }
#line 3196 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 152:
#line 1540 "parser.yxx" /* yacc.c:1646  */
    { (yyval.arg) = new AST::FloatLit((yyvsp[0].dValue)); }
#line 3202 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 153:
#line 1542 "parser.yxx" /* yacc.c:1646  */
    { (yyval.arg) = (yyvsp[0].setLit); }
#line 3208 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 154:
#line 1544 "parser.yxx" /* yacc.c:1646  */
    { 
        vector<int> as;
        ParserState* pp = static_cast<ParserState*>(parm);
        if (pp->intvararrays.get((yyvsp[0].sValue), as)) {
          AST::Array *ia = new AST::Array(as.size());
          for (int i=as.size(); i--;)
            ia->a[i] = new AST::IntVar(as[i]);
          (yyval.arg) = ia;
        } else if (pp->boolvararrays.get((yyvsp[0].sValue), as)) {
          AST::Array *ia = new AST::Array(as.size());
          for (int i=as.size(); i--;)
            ia->a[i] = new AST::BoolVar(as[i]);
          (yyval.arg) = ia;
        } else if (pp->setvararrays.get((yyvsp[0].sValue), as)) {
          AST::Array *ia = new AST::Array(as.size());
          for (int i=as.size(); i--;)
            ia->a[i] = new AST::SetVar(as[i]);
          (yyval.arg) = ia;
        } else {
          std::vector<int> is;
          int ival = 0;
          bool bval = false;
          if (pp->intvalarrays.get((yyvsp[0].sValue), is)) {
            AST::Array *v = new AST::Array(is.size());
            for (int i=is.size(); i--;)
              v->a[i] = new AST::IntLit(is[i]);
            (yyval.arg) = v;
          } else if (pp->boolvalarrays.get((yyvsp[0].sValue), is)) {
            AST::Array *v = new AST::Array(is.size());
            for (int i=is.size(); i--;)
              v->a[i] = new AST::BoolLit(is[i]);
            (yyval.arg) = v;
          } else if (pp->intvals.get((yyvsp[0].sValue), ival)) {
            (yyval.arg) = new AST::IntLit(ival);
          } else if (pp->boolvals.get((yyvsp[0].sValue), bval)) {
            (yyval.arg) = new AST::BoolLit(bval);
          } else {
            (yyval.arg) = getVarRefArg(pp,(yyvsp[0].sValue),true);
          }
        }
        free((yyvsp[0].sValue));
      }
#line 3255 "parser.tab.c" /* yacc.c:1646  */
    break;

  case 155:
#line 1587 "parser.yxx" /* yacc.c:1646  */
    { 
        ParserState* pp = static_cast<ParserState*>(parm);
        int i = -1;
        yyassert(pp, (yyvsp[-1].arg)->isInt(i), "Non-integer array index.");
        if (!pp->hadError)
          (yyval.arg) = getArrayElement(static_cast<ParserState*>(parm),(yyvsp[-3].sValue),i);
        else
          (yyval.arg) = new AST::IntLit(0); // keep things consistent
        free((yyvsp[-3].sValue));
      }
#line 3270 "parser.tab.c" /* yacc.c:1646  */
    break;


#line 3274 "parser.tab.c" /* yacc.c:1646  */
      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYEMPTY : YYTRANSLATE (yychar);

  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (parm, YY_("syntax error"));
#else
# define YYSYNTAX_ERROR yysyntax_error (&yymsg_alloc, &yymsg, \
                                        yyssp, yytoken)
      {
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        yysyntax_error_status = YYSYNTAX_ERROR;
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == 1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = (char *) YYSTACK_ALLOC (yymsg_alloc);
            if (!yymsg)
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = 2;
              }
            else
              {
                yysyntax_error_status = YYSYNTAX_ERROR;
                yymsgp = yymsg;
              }
          }
        yyerror (parm, yymsgp);
        if (yysyntax_error_status == 2)
          goto yyexhaustedlab;
      }
# undef YYSYNTAX_ERROR
#endif
    }



  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
         error, discard it.  */

      if (yychar <= YYEOF)
        {
          /* Return failure if at end of input.  */
          if (yychar == YYEOF)
            YYABORT;
        }
      else
        {
          yydestruct ("Error: discarding",
                      yytoken, &yylval, parm);
          yychar = YYEMPTY;
        }
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:

  /* Pacify compilers like GCC when the user code never invokes
     YYERROR and the label yyerrorlab therefore never appears in user
     code.  */
  if (/*CONSTCOND*/ 0)
     goto yyerrorlab;

  /* Do not reclaim the symbols of the rule whose action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;      /* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYTERROR;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
            {
              yyn = yytable[yyn];
              if (0 < yyn)
                break;
            }
        }

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
        YYABORT;


      yydestruct ("Error: popping",
                  yystos[yystate], yyvsp, parm);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#if !defined yyoverflow || YYERROR_VERBOSE
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (parm, YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval, parm);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  yystos[*yyssp], yyvsp, parm);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  return yyresult;
}

/* A Bison parser, made by GNU Bison 3.7.1.  */

/* Bison implementation for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015, 2018-2020 Free Software Foundation,
   Inc.

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

/* DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
   especially those whose name start with YY_ or yy_.  They are
   private implementation details that can be changed or removed.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "3.7.1"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 1

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1




/* First part of user prologue.  */

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
        if (pp->intvararrays.get(id, tmp) && offset<= tmp.size())
            return new AST::IntVar(tmp[offset-1]);
        if (pp->boolvararrays.get(id, tmp) && offset<= tmp.size())
            return new AST::BoolVar(tmp[offset-1]);
        if (pp->setvararrays.get(id, tmp) && offset<= tmp.size())
            return new AST::SetVar(tmp[offset-1]);

        if (pp->intvalarrays.get(id, tmp) && offset<= tmp.size())
            return new AST::IntLit(tmp[offset-1]);
        if (pp->boolvalarrays.get(id, tmp) && offset<= tmp.size())
            return new AST::BoolLit(tmp[offset-1]);
        vector<AST::SetLit> tmpS;
        if (pp->setvalarrays.get(id, tmpS) && offset<= tmpS.size())
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

void addDomainConstraint(
    ParserState* pp, std::string id, AST::Node* var, Option<AST::SetLit* >& dom
) {
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

    for (unsigned int i = 0; i < pp->intvars.size(); i++) {
        if (!pp->hadError) {
            try {
                pp->fg->newIntVar(static_cast<IntVarSpec*>(pp->intvars[i].second));
                IntVar* newiv = pp->fg->iv[pp->fg->intVarCount-1];
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
    for (unsigned int i = 0; i < pp->boolvars.size(); i++) {
        if (!pp->hadError) {
            try {
                pp->fg->newBoolVar(static_cast<BoolVarSpec*>(pp->boolvars[i].second));
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
    for (unsigned int i = 0; i < pp->setvars.size(); i++) {
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
    for (unsigned int i = pp->domainConstraints.size(); i--;) {
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
    for (unsigned int i = 0; i < a->a.size(); i++) {
        AST::SetLit* s = a->a[i]->getSet();
        if (s->empty())
            oss << "{}, ";
        else if (s->interval)
            oss << s->min << ".." << s->max << ", ";
        else {
            oss << "{";
            for (unsigned int j = 0; j < s->s.size(); j++) {
                oss << s->s[j];
                if (j < s->s.size()-1)
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
        FlatZinc::s->setOutput();
        
        if (pp.yyscanner)
            yylex_destroy(pp.yyscanner);
        if (pp.hadError) abort();
    }

}



# ifndef YY_CAST
#  ifdef __cplusplus
#   define YY_CAST(Type, Val) static_cast<Type> (Val)
#   define YY_REINTERPRET_CAST(Type, Val) reinterpret_cast<Type> (Val)
#  else
#   define YY_CAST(Type, Val) ((Type) (Val))
#   define YY_REINTERPRET_CAST(Type, Val) ((Type) (Val))
#  endif
# endif
# ifndef YY_NULLPTR
#  if defined __cplusplus
#   if 201103L <= __cplusplus
#    define YY_NULLPTR nullptr
#   else
#    define YY_NULLPTR 0
#   endif
#  else
#   define YY_NULLPTR ((void*)0)
#  endif
# endif

#include <chuffed/flatzinc/parser.tab.h>
/* Symbol kind.  */
enum yysymbol_kind_t
{
  YYSYMBOL_YYEMPTY = -2,
  YYSYMBOL_YYEOF = 0,                      /* "end of file"  */
  YYSYMBOL_YYerror = 1,                    /* error  */
  YYSYMBOL_YYUNDEF = 2,                    /* "invalid token"  */
  YYSYMBOL_INT_LIT = 3,                    /* INT_LIT  */
  YYSYMBOL_BOOL_LIT = 4,                   /* BOOL_LIT  */
  YYSYMBOL_FLOAT_LIT = 5,                  /* FLOAT_LIT  */
  YYSYMBOL_ID = 6,                         /* ID  */
  YYSYMBOL_STRING_LIT = 7,                 /* STRING_LIT  */
  YYSYMBOL_VAR = 8,                        /* VAR  */
  YYSYMBOL_PAR = 9,                        /* PAR  */
  YYSYMBOL_ANNOTATION = 10,                /* ANNOTATION  */
  YYSYMBOL_ANY = 11,                       /* ANY  */
  YYSYMBOL_ARRAY = 12,                     /* ARRAY  */
  YYSYMBOL_BOOLTOK = 13,                   /* BOOLTOK  */
  YYSYMBOL_CASE = 14,                      /* CASE  */
  YYSYMBOL_COLONCOLON = 15,                /* COLONCOLON  */
  YYSYMBOL_CONSTRAINT = 16,                /* CONSTRAINT  */
  YYSYMBOL_DEFAULT = 17,                   /* DEFAULT  */
  YYSYMBOL_DOTDOT = 18,                    /* DOTDOT  */
  YYSYMBOL_ELSE = 19,                      /* ELSE  */
  YYSYMBOL_ELSEIF = 20,                    /* ELSEIF  */
  YYSYMBOL_ENDIF = 21,                     /* ENDIF  */
  YYSYMBOL_ENUM = 22,                      /* ENUM  */
  YYSYMBOL_FLOATTOK = 23,                  /* FLOATTOK  */
  YYSYMBOL_FUNCTION = 24,                  /* FUNCTION  */
  YYSYMBOL_IF = 25,                        /* IF  */
  YYSYMBOL_INCLUDE = 26,                   /* INCLUDE  */
  YYSYMBOL_INTTOK = 27,                    /* INTTOK  */
  YYSYMBOL_LET = 28,                       /* LET  */
  YYSYMBOL_MAXIMIZE = 29,                  /* MAXIMIZE  */
  YYSYMBOL_MINIMIZE = 30,                  /* MINIMIZE  */
  YYSYMBOL_OF = 31,                        /* OF  */
  YYSYMBOL_SATISFY = 32,                   /* SATISFY  */
  YYSYMBOL_OUTPUT = 33,                    /* OUTPUT  */
  YYSYMBOL_PREDICATE = 34,                 /* PREDICATE  */
  YYSYMBOL_RECORD = 35,                    /* RECORD  */
  YYSYMBOL_SET = 36,                       /* SET  */
  YYSYMBOL_SHOW = 37,                      /* SHOW  */
  YYSYMBOL_SHOWCOND = 38,                  /* SHOWCOND  */
  YYSYMBOL_SOLVE = 39,                     /* SOLVE  */
  YYSYMBOL_STRING = 40,                    /* STRING  */
  YYSYMBOL_TEST = 41,                      /* TEST  */
  YYSYMBOL_THEN = 42,                      /* THEN  */
  YYSYMBOL_TUPLE = 43,                     /* TUPLE  */
  YYSYMBOL_TYPE = 44,                      /* TYPE  */
  YYSYMBOL_VARIANT_RECORD = 45,            /* VARIANT_RECORD  */
  YYSYMBOL_WHERE = 46,                     /* WHERE  */
  YYSYMBOL_47_ = 47,                       /* ';'  */
  YYSYMBOL_48_ = 48,                       /* '('  */
  YYSYMBOL_49_ = 49,                       /* ')'  */
  YYSYMBOL_50_ = 50,                       /* ','  */
  YYSYMBOL_51_ = 51,                       /* ':'  */
  YYSYMBOL_52_ = 52,                       /* '['  */
  YYSYMBOL_53_ = 53,                       /* ']'  */
  YYSYMBOL_54_ = 54,                       /* '='  */
  YYSYMBOL_55_ = 55,                       /* '{'  */
  YYSYMBOL_56_ = 56,                       /* '}'  */
  YYSYMBOL_YYACCEPT = 57,                  /* $accept  */
  YYSYMBOL_model = 58,                     /* model  */
  YYSYMBOL_preddecl_items = 59,            /* preddecl_items  */
  YYSYMBOL_preddecl_items_head = 60,       /* preddecl_items_head  */
  YYSYMBOL_vardecl_items = 61,             /* vardecl_items  */
  YYSYMBOL_vardecl_items_head = 62,        /* vardecl_items_head  */
  YYSYMBOL_constraint_items = 63,          /* constraint_items  */
  YYSYMBOL_constraint_items_head = 64,     /* constraint_items_head  */
  YYSYMBOL_preddecl_item = 65,             /* preddecl_item  */
  YYSYMBOL_pred_arg_list = 66,             /* pred_arg_list  */
  YYSYMBOL_pred_arg_list_head = 67,        /* pred_arg_list_head  */
  YYSYMBOL_pred_arg = 68,                  /* pred_arg  */
  YYSYMBOL_pred_arg_type = 69,             /* pred_arg_type  */
  YYSYMBOL_pred_arg_simple_type = 70,      /* pred_arg_simple_type  */
  YYSYMBOL_pred_array_init = 71,           /* pred_array_init  */
  YYSYMBOL_pred_array_init_arg = 72,       /* pred_array_init_arg  */
  YYSYMBOL_vardecl_item = 73,              /* vardecl_item  */
  YYSYMBOL_int_init = 74,                  /* int_init  */
  YYSYMBOL_int_init_list = 75,             /* int_init_list  */
  YYSYMBOL_int_init_list_head = 76,        /* int_init_list_head  */
  YYSYMBOL_list_tail = 77,                 /* list_tail  */
  YYSYMBOL_int_var_array_literal = 78,     /* int_var_array_literal  */
  YYSYMBOL_float_init = 79,                /* float_init  */
  YYSYMBOL_float_init_list = 80,           /* float_init_list  */
  YYSYMBOL_float_init_list_head = 81,      /* float_init_list_head  */
  YYSYMBOL_float_var_array_literal = 82,   /* float_var_array_literal  */
  YYSYMBOL_bool_init = 83,                 /* bool_init  */
  YYSYMBOL_bool_init_list = 84,            /* bool_init_list  */
  YYSYMBOL_bool_init_list_head = 85,       /* bool_init_list_head  */
  YYSYMBOL_bool_var_array_literal = 86,    /* bool_var_array_literal  */
  YYSYMBOL_set_init = 87,                  /* set_init  */
  YYSYMBOL_set_init_list = 88,             /* set_init_list  */
  YYSYMBOL_set_init_list_head = 89,        /* set_init_list_head  */
  YYSYMBOL_set_var_array_literal = 90,     /* set_var_array_literal  */
  YYSYMBOL_vardecl_int_var_array_init = 91, /* vardecl_int_var_array_init  */
  YYSYMBOL_vardecl_bool_var_array_init = 92, /* vardecl_bool_var_array_init  */
  YYSYMBOL_vardecl_float_var_array_init = 93, /* vardecl_float_var_array_init  */
  YYSYMBOL_vardecl_set_var_array_init = 94, /* vardecl_set_var_array_init  */
  YYSYMBOL_constraint_item = 95,           /* constraint_item  */
  YYSYMBOL_solve_item = 96,                /* solve_item  */
  YYSYMBOL_int_ti_expr_tail = 97,          /* int_ti_expr_tail  */
  YYSYMBOL_bool_ti_expr_tail = 98,         /* bool_ti_expr_tail  */
  YYSYMBOL_float_ti_expr_tail = 99,        /* float_ti_expr_tail  */
  YYSYMBOL_set_literal = 100,              /* set_literal  */
  YYSYMBOL_int_list = 101,                 /* int_list  */
  YYSYMBOL_int_list_head = 102,            /* int_list_head  */
  YYSYMBOL_bool_list = 103,                /* bool_list  */
  YYSYMBOL_bool_list_head = 104,           /* bool_list_head  */
  YYSYMBOL_float_list = 105,               /* float_list  */
  YYSYMBOL_float_list_head = 106,          /* float_list_head  */
  YYSYMBOL_set_literal_list = 107,         /* set_literal_list  */
  YYSYMBOL_set_literal_list_head = 108,    /* set_literal_list_head  */
  YYSYMBOL_flat_expr_list = 109,           /* flat_expr_list  */
  YYSYMBOL_flat_expr = 110,                /* flat_expr  */
  YYSYMBOL_non_array_expr_opt = 111,       /* non_array_expr_opt  */
  YYSYMBOL_non_array_expr = 112,           /* non_array_expr  */
  YYSYMBOL_non_array_expr_list = 113,      /* non_array_expr_list  */
  YYSYMBOL_non_array_expr_list_head = 114, /* non_array_expr_list_head  */
  YYSYMBOL_solve_expr = 115,               /* solve_expr  */
  YYSYMBOL_minmax = 116,                   /* minmax  */
  YYSYMBOL_annotations = 117,              /* annotations  */
  YYSYMBOL_annotations_head = 118,         /* annotations_head  */
  YYSYMBOL_annotation = 119,               /* annotation  */
  YYSYMBOL_annotation_list = 120,          /* annotation_list  */
  YYSYMBOL_annotation_expr = 121,          /* annotation_expr  */
  YYSYMBOL_ann_non_array_expr = 122        /* ann_non_array_expr  */
};
typedef enum yysymbol_kind_t yysymbol_kind_t;




#ifdef short
# undef short
#endif

/* On compilers that do not define __PTRDIFF_MAX__ etc., make sure
   <limits.h> and (if available) <stdint.h> are included
   so that the code can choose integer types of a good width.  */

#ifndef __PTRDIFF_MAX__
# include <limits.h> /* INFRINGES ON USER NAME SPACE */
# if defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stdint.h> /* INFRINGES ON USER NAME SPACE */
#  define YY_STDINT_H
# endif
#endif

/* Narrow types that promote to a signed type and that can represent a
   signed or unsigned integer of at least N bits.  In tables they can
   save space and decrease cache pressure.  Promoting to a signed type
   helps avoid bugs in integer arithmetic.  */

#ifdef __INT_LEAST8_MAX__
typedef __INT_LEAST8_TYPE__ yytype_int8;
#elif defined YY_STDINT_H
typedef int_least8_t yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef __INT_LEAST16_MAX__
typedef __INT_LEAST16_TYPE__ yytype_int16;
#elif defined YY_STDINT_H
typedef int_least16_t yytype_int16;
#else
typedef short yytype_int16;
#endif

#if defined __UINT_LEAST8_MAX__ && __UINT_LEAST8_MAX__ <= __INT_MAX__
typedef __UINT_LEAST8_TYPE__ yytype_uint8;
#elif (!defined __UINT_LEAST8_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST8_MAX <= INT_MAX)
typedef uint_least8_t yytype_uint8;
#elif !defined __UINT_LEAST8_MAX__ && UCHAR_MAX <= INT_MAX
typedef unsigned char yytype_uint8;
#else
typedef short yytype_uint8;
#endif

#if defined __UINT_LEAST16_MAX__ && __UINT_LEAST16_MAX__ <= __INT_MAX__
typedef __UINT_LEAST16_TYPE__ yytype_uint16;
#elif (!defined __UINT_LEAST16_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST16_MAX <= INT_MAX)
typedef uint_least16_t yytype_uint16;
#elif !defined __UINT_LEAST16_MAX__ && USHRT_MAX <= INT_MAX
typedef unsigned short yytype_uint16;
#else
typedef int yytype_uint16;
#endif

#ifndef YYPTRDIFF_T
# if defined __PTRDIFF_TYPE__ && defined __PTRDIFF_MAX__
#  define YYPTRDIFF_T __PTRDIFF_TYPE__
#  define YYPTRDIFF_MAXIMUM __PTRDIFF_MAX__
# elif defined PTRDIFF_MAX
#  ifndef ptrdiff_t
#   include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  endif
#  define YYPTRDIFF_T ptrdiff_t
#  define YYPTRDIFF_MAXIMUM PTRDIFF_MAX
# else
#  define YYPTRDIFF_T long
#  define YYPTRDIFF_MAXIMUM LONG_MAX
# endif
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned
# endif
#endif

#define YYSIZE_MAXIMUM                                  \
  YY_CAST (YYPTRDIFF_T,                                 \
           (YYPTRDIFF_MAXIMUM < YY_CAST (YYSIZE_T, -1)  \
            ? YYPTRDIFF_MAXIMUM                         \
            : YY_CAST (YYSIZE_T, -1)))

#define YYSIZEOF(X) YY_CAST (YYPTRDIFF_T, sizeof (X))


/* Stored state numbers (used for stacks). */
typedef yytype_int16 yy_state_t;

/* State numbers in computations.  */
typedef int yy_state_fast_t;

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


#ifndef YY_ATTRIBUTE_PURE
# if defined __GNUC__ && 2 < __GNUC__ + (96 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_PURE __attribute__ ((__pure__))
# else
#  define YY_ATTRIBUTE_PURE
# endif
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# if defined __GNUC__ && 2 < __GNUC__ + (7 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_UNUSED __attribute__ ((__unused__))
# else
#  define YY_ATTRIBUTE_UNUSED
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(E) ((void) (E))
#else
# define YYUSE(E) /* empty */
#endif

#if defined __GNUC__ && ! defined __ICC && 407 <= __GNUC__ * 100 + __GNUC_MINOR__
/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                            \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")              \
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# define YY_IGNORE_MAYBE_UNINITIALIZED_END      \
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

#if defined __cplusplus && defined __GNUC__ && ! defined __ICC && 6 <= __GNUC__
# define YY_IGNORE_USELESS_CAST_BEGIN                          \
    _Pragma ("GCC diagnostic push")                            \
    _Pragma ("GCC diagnostic ignored \"-Wuseless-cast\"")
# define YY_IGNORE_USELESS_CAST_END            \
    _Pragma ("GCC diagnostic pop")
#endif
#ifndef YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_END
#endif


#define YY_ASSERT(E) ((void) (0 && (E)))

#if 1

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
#endif /* 1 */

#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yy_state_t yyss_alloc;
  YYSTYPE yyvs_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (YYSIZEOF (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (YYSIZEOF (yy_state_t) + YYSIZEOF (YYSTYPE)) \
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
        YYPTRDIFF_T yynewbytes;                                         \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * YYSIZEOF (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / YYSIZEOF (*yyptr);                        \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, YY_CAST (YYSIZE_T, (Count)) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYPTRDIFF_T yyi;                      \
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
#define YYLAST   341

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  57
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  66
/* YYNRULES -- Number of rules.  */
#define YYNRULES  157
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  340

/* YYMAXUTOK -- Last valid token kind.  */
#define YYMAXUTOK   301


/* YYTRANSLATE(TOKEN-NUM) -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, with out-of-bounds checking.  */
#define YYTRANSLATE(YYX)                                \
  (0 <= (YYX) && (YYX) <= YYMAXUTOK                     \
   ? YY_CAST (yysymbol_kind_t, yytranslate[YYX])        \
   : YYSYMBOL_YYUNDEF)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex.  */
static const yytype_int8 yytranslate[] =
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
static const yytype_int16 yyrline[] =
{
       0,   486,   486,   488,   490,   493,   494,   498,   503,   511,
     512,   516,   521,   529,   530,   537,   539,   541,   544,   545,
     548,   551,   552,   553,   554,   557,   558,   559,   560,   563,
     564,   567,   568,   575,   607,   638,   645,   677,   703,   713,
     726,   783,   834,   842,   896,   909,   922,   930,   945,   949,
     964,   988,   991,   997,  1002,  1008,  1010,  1013,  1019,  1023,
    1038,  1062,  1065,  1071,  1076,  1083,  1089,  1093,  1108,  1132,
    1135,  1141,  1146,  1153,  1156,  1160,  1175,  1199,  1202,  1208,
    1213,  1220,  1227,  1230,  1237,  1240,  1247,  1250,  1257,  1260,
    1266,  1284,  1305,  1328,  1336,  1353,  1357,  1361,  1367,  1371,
    1385,  1386,  1393,  1397,  1406,  1409,  1415,  1420,  1428,  1431,
    1437,  1442,  1450,  1453,  1459,  1464,  1472,  1475,  1481,  1487,
    1499,  1503,  1510,  1514,  1521,  1524,  1530,  1534,  1538,  1542,
    1546,  1595,  1609,  1612,  1618,  1622,  1633,  1654,  1684,  1706,
    1707,  1715,  1718,  1724,  1728,  1735,  1740,  1746,  1750,  1757,
    1761,  1767,  1771,  1775,  1779,  1783,  1826,  1837
};
#endif

/** Accessing symbol of state STATE.  */
#define YY_ACCESSING_SYMBOL(State) YY_CAST (yysymbol_kind_t, yystos[State])

#if 1
/* The user-facing name of the symbol whose (internal) number is
   YYSYMBOL.  No bounds checking.  */
static const char *yysymbol_name (yysymbol_kind_t yysymbol) YY_ATTRIBUTE_UNUSED;

/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "\"end of file\"", "error", "\"invalid token\"", "INT_LIT", "BOOL_LIT",
  "FLOAT_LIT", "ID", "STRING_LIT", "VAR", "PAR", "ANNOTATION", "ANY",
  "ARRAY", "BOOLTOK", "CASE", "COLONCOLON", "CONSTRAINT", "DEFAULT",
  "DOTDOT", "ELSE", "ELSEIF", "ENDIF", "ENUM", "FLOATTOK", "FUNCTION",
  "IF", "INCLUDE", "INTTOK", "LET", "MAXIMIZE", "MINIMIZE", "OF",
  "SATISFY", "OUTPUT", "PREDICATE", "RECORD", "SET", "SHOW", "SHOWCOND",
  "SOLVE", "STRING", "TEST", "THEN", "TUPLE", "TYPE", "VARIANT_RECORD",
  "WHERE", "';'", "'('", "')'", "','", "':'", "'['", "']'", "'='", "'{'",
  "'}'", "$accept", "model", "preddecl_items", "preddecl_items_head",
  "vardecl_items", "vardecl_items_head", "constraint_items",
  "constraint_items_head", "preddecl_item", "pred_arg_list",
  "pred_arg_list_head", "pred_arg", "pred_arg_type",
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

static const char *
yysymbol_name (yysymbol_kind_t yysymbol)
{
  return yytname[yysymbol];
}
#endif

#ifdef YYPRINT
/* YYTOKNUM[NUM] -- (External) token number corresponding to the
   (internal) symbol number NUM (which must be that of a token).  */
static const yytype_int16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298,   299,   300,   301,    59,    40,    41,
      44,    58,    91,    93,    61,   123,   125
};
#endif

#define YYPACT_NINF (-124)

#define yypact_value_is_default(Yyn) \
  ((Yyn) == YYPACT_NINF)

#define YYTABLE_NINF (-1)

#define yytable_value_is_error(Yyn) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int16 yypact[] =
{
       4,    38,    76,    45,     4,    44,    49,  -124,    75,   105,
      60,    72,  -124,   100,   137,   131,    45,   109,   102,   110,
    -124,    27,   151,  -124,  -124,   134,   147,   112,   113,   115,
     164,   163,    14,  -124,   114,   121,   166,   136,   131,   130,
     135,  -124,   178,  -124,   107,   138,  -124,  -124,   155,   139,
     142,  -124,   144,  -124,  -124,  -124,    14,  -124,  -124,   146,
     148,   183,   188,   191,   181,   185,   150,  -124,   199,  -124,
     133,   185,   157,   159,  -124,  -124,   185,  -124,    25,    14,
    -124,    27,  -124,   202,   158,   206,   156,   208,   160,   185,
     185,   185,   211,    61,   161,   196,   212,  -124,    84,   214,
    -124,    17,  -124,  -124,   169,   209,  -124,   -24,  -124,  -124,
    -124,  -124,   218,  -124,  -124,  -124,  -124,   172,   172,   172,
     167,   210,  -124,  -124,    54,  -124,    61,   137,  -124,  -124,
    -124,  -124,    56,    61,   185,   210,  -124,  -124,   177,    56,
    -124,    36,  -124,  -124,   179,  -124,  -124,  -124,   119,    56,
     228,    25,   203,   185,    56,  -124,  -124,  -124,   205,   230,
      61,    18,  -124,    74,   182,  -124,  -124,   189,    56,  -124,
     186,   192,   185,    84,   185,  -124,   193,  -124,  -124,  -124,
    -124,    71,   172,  -124,   106,  -124,    55,   194,   195,    61,
    -124,  -124,    56,   197,  -124,    56,  -124,  -124,  -124,  -124,
     241,   107,  -124,  -124,   132,   198,   200,   216,   201,  -124,
    -124,  -124,  -124,  -124,  -124,   204,  -124,   222,   207,   215,
     219,   248,   249,    14,   250,  -124,    14,   253,   254,   255,
     185,   185,   220,   185,   221,   185,   185,   185,   213,   223,
     256,   224,   257,   225,   226,   227,   217,   231,   185,   232,
     185,   233,  -124,   234,  -124,   235,  -124,   261,   268,   236,
     137,   237,   143,  -124,    12,  -124,     1,  -124,   229,   146,
     239,   148,   242,   240,   243,  -124,  -124,   244,  -124,   245,
     238,  -124,   247,  -124,   251,   252,  -124,   258,  -124,   259,
     263,  -124,  -124,  -124,  -124,    48,  -124,    89,  -124,   271,
    -124,   143,  -124,   272,  -124,    12,  -124,   273,  -124,     1,
    -124,   210,  -124,   262,   264,   265,  -124,   266,   270,  -124,
     269,  -124,   274,  -124,   275,  -124,  -124,    48,  -124,   286,
    -124,    89,  -124,  -124,  -124,  -124,  -124,   276,  -124,  -124
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
      55,     0,     0,     0,     0,   141,     0,    96,    56,   105,
     141,   141,     0,     0,    13,    10,   141,    23,     0,     0,
      15,    56,    17,     0,     0,    56,     0,    56,     0,   141,
     141,   141,     0,     0,     0,   142,     0,   107,     0,     0,
      91,     0,     2,    14,     0,     0,    31,     0,    29,    26,
      19,    20,     0,   111,    99,   115,   101,   124,   124,   124,
       0,   152,   151,   153,   155,   157,     0,   104,   154,   143,
     146,   149,     0,     0,   141,   127,   126,   128,   130,   132,
     129,     0,   120,   122,     0,   140,   139,    93,     0,     0,
       0,     0,     0,   141,     0,    33,    34,    35,     0,     0,
       0,     0,   147,     0,     0,    38,   144,     0,     0,   134,
       0,    55,   141,     0,   141,   136,   137,    94,    37,    32,
      30,     0,   124,   125,     0,   103,     0,   155,     0,     0,
     150,   102,     0,     0,   123,    56,   133,    90,   121,    92,
       0,     0,    21,    36,     0,     0,     0,     0,     0,   145,
     156,   148,    39,   131,   135,     0,    22,     0,     0,     0,
       0,     0,     0,     0,     0,   138,     0,     0,     0,     0,
     141,   141,     0,   141,     0,   141,   141,   141,     0,     0,
       0,     0,     0,    82,    84,    86,     0,     0,   141,     0,
     141,     0,    40,     0,    41,     0,    42,   108,   112,     0,
     104,    88,    51,    83,    69,    85,    61,    87,     0,    55,
       0,    55,     0,     0,     0,    43,    48,    49,    53,     0,
      55,    66,    67,    71,     0,    55,    58,    59,    63,     0,
      55,    45,   109,    46,   113,   116,    44,    77,    89,     0,
      57,    56,    52,     0,    73,    56,    70,     0,    65,    56,
      62,     0,   118,     0,    55,    75,    79,     0,    55,    74,
       0,    54,     0,    72,     0,    64,    47,    56,   117,     0,
      81,    56,    78,    50,    68,    60,   119,     0,    80,    76
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -124,  -124,  -124,  -124,  -124,  -124,  -124,  -124,   293,  -124,
    -124,   260,  -124,   -43,  -124,   149,   285,     2,  -124,  -124,
     -50,  -124,    -4,  -124,  -124,  -124,     3,  -124,  -124,  -124,
     -25,  -124,  -124,  -124,  -124,  -124,  -124,  -124,   278,  -124,
      -1,   103,   117,   -90,  -123,  -124,  -124,    52,  -124,    53,
    -124,  -124,  -124,   145,  -107,  -112,  -124,  -124,  -124,  -124,
     -57,  -124,   -88,   165,  -124,   162
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     2,     3,     4,    15,    16,    37,    38,     5,    49,
      50,    51,    52,    53,   107,   108,    17,   278,   279,   280,
      69,   263,   288,   289,   290,   267,   283,   284,   285,   265,
     316,   317,   318,   298,   252,   254,   256,   275,    39,    72,
      54,    28,    29,   140,    34,    35,   268,    59,   270,    60,
     313,   314,   141,   142,   155,   143,   170,   171,   177,   148,
      94,    95,   162,   163,   130,   131
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_int16 yytable[] =
{
      82,    77,    18,   128,   164,   129,   286,   287,    27,    86,
      88,   156,   157,   100,   101,    18,   281,     8,   282,   104,
     165,   121,   122,   123,   187,   125,   151,   169,   105,   152,
       8,    66,   117,   118,   119,    44,   128,   178,     1,    45,
      46,    12,   183,   128,     6,   166,   145,   146,     8,   147,
      47,   311,   106,     9,    12,    84,   193,    10,    11,   135,
     136,   137,   138,    48,   121,   122,   123,   124,   125,    14,
     128,   128,    12,   127,     8,   203,     7,   167,   109,   201,
     212,    13,    14,   214,    46,   172,   173,   135,   136,   137,
     138,    20,   311,    22,    47,   315,   182,    21,    12,   128,
      14,   211,   160,   127,   209,   189,   161,    48,     8,     8,
       8,   127,    30,   126,   204,   197,   127,   199,    23,   205,
      46,   196,   175,    31,   189,   176,    14,   190,    24,   206,
      47,    32,    12,    12,    12,     8,   139,   273,   202,   127,
      33,    25,   207,    48,   127,    23,   276,    36,    93,   277,
      33,    57,    58,    42,    55,    24,    41,    43,   216,    12,
      26,    14,    14,    61,    62,    56,    63,    64,   217,    65,
      67,    68,    70,   238,   239,    71,   241,    74,   243,   244,
     245,    98,    75,   208,    76,    99,    79,    26,    80,    89,
      78,   259,    81,   261,    90,    83,    85,    91,    87,    92,
      93,    96,    97,   218,   102,   312,   103,   319,   111,   112,
     113,   133,   114,   115,   120,   132,   116,   144,   134,   292,
     158,   294,   232,   149,   153,   234,   154,   150,   159,   168,
     302,   179,   174,   185,   181,   306,   184,   336,   191,   194,
     310,   319,   195,   192,   215,   200,   161,   223,   210,   221,
     213,   222,   224,   226,   230,   231,   233,   225,   227,   235,
     236,   237,   248,   250,   328,    57,   228,   246,   332,   257,
     229,   240,   242,    58,   320,   322,   324,   247,   249,   251,
     253,   255,   291,   258,   260,   262,   264,   266,   301,   337,
     272,   274,   293,   296,   295,   297,   299,    19,   300,   303,
     180,    40,   305,   321,   304,   325,   338,   219,   323,   269,
     307,   271,   308,   309,   327,   326,    73,   329,   198,   330,
     331,   220,   333,   188,     0,   186,     0,   334,   335,   339,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   110
};

static const yytype_int16 yycheck[] =
{
      50,    44,     3,    93,   127,    93,     5,     6,     9,    59,
      60,   118,   119,    70,    71,    16,     4,     3,     6,    76,
     132,     3,     4,     5,     6,     7,    50,   139,     3,    53,
       3,    32,    89,    90,    91,     8,   126,   149,    34,    12,
      13,    27,   154,   133,     6,   133,    29,    30,     3,    32,
      23,     3,    27,     8,    27,    56,   168,    12,    13,     3,
       4,     5,     6,    36,     3,     4,     5,     6,     7,    55,
     160,   161,    27,    55,     3,   182,     0,   134,    79,     8,
     192,    36,    55,   195,    13,    49,    50,     3,     4,     5,
       6,    47,     3,    18,    23,     6,   153,    48,    27,   189,
      55,   189,    48,    55,    49,    50,    52,    36,     3,     3,
       3,    55,    52,    52,     8,   172,    55,   174,    13,    13,
      13,   171,     3,    51,    50,     6,    55,    53,    23,    23,
      23,    31,    27,    27,    27,     3,    52,   260,   181,    55,
       3,    36,    36,    36,    55,    13,     3,    16,    15,     6,
       3,     4,     5,    51,     3,    23,    47,    47,   201,    27,
      55,    55,    55,    51,    51,    31,    51,     3,    36,     6,
      56,    50,     6,   230,   231,    39,   233,    47,   235,   236,
     237,    48,    47,   184,     6,    52,    31,    55,    49,     6,
      52,   248,    50,   250,     6,    51,    50,     6,    50,    18,
      15,    51,     3,   204,    47,   295,    47,   297,     6,    51,
       4,    15,    56,     5,     3,    54,    56,     3,     6,   269,
      53,   271,   223,    54,     6,   226,    54,    18,    18,    52,
     280,     3,    53,     3,    31,   285,    31,   327,    56,    53,
     290,   331,    50,    54,     3,    52,    52,    31,    53,    51,
      53,    51,    51,    31,     6,     6,     6,    53,    51,     6,
       6,     6,     6,     6,   314,     4,    51,    54,   318,    52,
      51,    51,    51,     5,     3,     3,     3,    54,    54,    54,
      54,    54,    53,    52,    52,    52,    52,    52,    50,     3,
      54,    54,    53,    53,    52,    52,    52,     4,    53,    52,
     151,    16,    50,   301,    53,   309,   331,   204,   305,   257,
      52,   258,    53,    50,    50,    53,    38,    52,   173,    53,
      50,   204,    53,   161,    -1,   160,    -1,    53,    53,    53,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    81
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_int8 yystos[] =
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
       3,     3,     4,     5,     6,     7,    52,    55,   100,   119,
     121,   122,    54,    15,     6,     3,     4,     5,     6,    52,
     100,   109,   110,   112,     3,    29,    30,    32,   116,    54,
      18,    50,    53,     6,    54,   111,   111,   111,    53,    18,
      48,    52,   119,   120,   101,   112,   119,   117,    52,   112,
     113,   114,    49,    50,    53,     3,     6,   115,   112,     3,
      72,    31,   117,   112,    31,     3,   120,     6,   122,    50,
      53,    56,    54,   112,    53,    50,    77,   117,   110,   117,
      52,     8,    70,   111,     8,    13,    23,    36,    97,    49,
      53,   119,   112,    53,   112,     3,    70,    36,    97,    98,
      99,    51,    51,    31,    51,    53,    31,    51,    51,    51,
       6,     6,    97,     6,    97,     6,     6,     6,   117,   117,
      51,   117,    51,   117,   117,   117,    54,    54,     6,    54,
       6,    54,    91,    54,    92,    54,    93,    52,    52,   117,
      52,   117,    52,    78,    52,    86,    52,    82,   103,   104,
     105,   106,    54,   101,    54,    94,     3,     6,    74,    75,
      76,     4,     6,    83,    84,    85,     5,     6,    79,    80,
      81,    53,    77,    53,    77,    52,    53,    52,    90,    52,
      53,    50,    77,    52,    53,    50,    77,    52,    53,    50,
      77,     3,   100,   107,   108,     6,    87,    88,    89,   100,
       3,    74,     3,    83,     3,    79,    53,    50,    77,    52,
      53,    50,    77,    53,    53,    53,   100,     3,    87,    53
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_int8 yyr1[] =
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
     112,   112,   113,   113,   114,   114,   115,   115,   115,   116,
     116,   117,   117,   118,   118,   119,   119,   120,   120,   121,
     121,   122,   122,   122,   122,   122,   122,   122
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_int8 yyr2[] =
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
       1,     4,     0,     2,     1,     3,     1,     1,     4,     1,
       1,     0,     1,     2,     3,     4,     1,     1,     3,     1,
       3,     1,     1,     1,     1,     1,     4,     1
};


enum { YYENOMEM = -2 };

#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                    \
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

/* Backward compatibility with an undocumented macro.
   Use YYerror or YYUNDEF. */
#define YYERRCODE YYUNDEF


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
# ifndef YY_LOCATION_PRINT
#  define YY_LOCATION_PRINT(File, Loc) ((void) 0)
# endif


# define YY_SYMBOL_PRINT(Title, Kind, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Kind, Value, parm); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*-----------------------------------.
| Print this symbol's value on YYO.  |
`-----------------------------------*/

static void
yy_symbol_value_print (FILE *yyo,
                       yysymbol_kind_t yykind, YYSTYPE const * const yyvaluep, void *parm)
{
  FILE *yyoutput = yyo;
  YYUSE (yyoutput);
  YYUSE (parm);
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yykind < YYNTOKENS)
    YYPRINT (yyo, yytoknum[yykind], *yyvaluep);
# endif
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YYUSE (yykind);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}


/*---------------------------.
| Print this symbol on YYO.  |
`---------------------------*/

static void
yy_symbol_print (FILE *yyo,
                 yysymbol_kind_t yykind, YYSTYPE const * const yyvaluep, void *parm)
{
  YYFPRINTF (yyo, "%s %s (",
             yykind < YYNTOKENS ? "token" : "nterm", yysymbol_name (yykind));

  yy_symbol_value_print (yyo, yykind, yyvaluep, parm);
  YYFPRINTF (yyo, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yy_state_t *yybottom, yy_state_t *yytop)
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
yy_reduce_print (yy_state_t *yyssp, YYSTYPE *yyvsp,
                 int yyrule, void *parm)
{
  int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %d):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       YY_ACCESSING_SYMBOL (+yyssp[yyi + 1 - yynrhs]),
                       &yyvsp[(yyi + 1) - (yynrhs)], parm);
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
# define YYDPRINTF(Args) ((void) 0)
# define YY_SYMBOL_PRINT(Title, Kind, Value, Location)
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


/* Context of a parse error.  */
typedef struct
{
  yy_state_t *yyssp;
  yysymbol_kind_t yytoken;
} yypcontext_t;

/* Put in YYARG at most YYARGN of the expected tokens given the
   current YYCTX, and return the number of tokens stored in YYARG.  If
   YYARG is null, return the number of expected tokens (guaranteed to
   be less than YYNTOKENS).  Return YYENOMEM on memory exhaustion.
   Return 0 if there are more than YYARGN expected tokens, yet fill
   YYARG up to YYARGN. */
static int
yypcontext_expected_tokens (const yypcontext_t *yyctx,
                            yysymbol_kind_t yyarg[], int yyargn)
{
  /* Actual size of YYARG. */
  int yycount = 0;
  int yyn = yypact[+*yyctx->yyssp];
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
        if (yycheck[yyx + yyn] == yyx && yyx != YYSYMBOL_YYerror
            && !yytable_value_is_error (yytable[yyx + yyn]))
          {
            if (!yyarg)
              ++yycount;
            else if (yycount == yyargn)
              return 0;
            else
              yyarg[yycount++] = YY_CAST (yysymbol_kind_t, yyx);
          }
    }
  if (yyarg && yycount == 0 && 0 < yyargn)
    yyarg[0] = YYSYMBOL_YYEMPTY;
  return yycount;
}




#ifndef yystrlen
# if defined __GLIBC__ && defined _STRING_H
#  define yystrlen(S) (YY_CAST (YYPTRDIFF_T, strlen (S)))
# else
/* Return the length of YYSTR.  */
static YYPTRDIFF_T
yystrlen (const char *yystr)
{
  YYPTRDIFF_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
# endif
#endif

#ifndef yystpcpy
# if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#  define yystpcpy stpcpy
# else
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
# endif
#endif

#ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYPTRDIFF_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYPTRDIFF_T yyn = 0;
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
            else
              goto append;

          append:
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

  if (yyres)
    return yystpcpy (yyres, yystr) - yyres;
  else
    return yystrlen (yystr);
}
#endif


static int
yy_syntax_error_arguments (const yypcontext_t *yyctx,
                           yysymbol_kind_t yyarg[], int yyargn)
{
  /* Actual size of YYARG. */
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
  if (yyctx->yytoken != YYSYMBOL_YYEMPTY)
    {
      int yyn;
      if (yyarg)
        yyarg[yycount] = yyctx->yytoken;
      ++yycount;
      yyn = yypcontext_expected_tokens (yyctx,
                                        yyarg ? yyarg + 1 : yyarg, yyargn - 1);
      if (yyn == YYENOMEM)
        return YYENOMEM;
      else
        yycount += yyn;
    }
  return yycount;
}

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.

   Return 0 if *YYMSG was successfully written.  Return -1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return YYENOMEM if the
   required number of bytes is too large to store.  */
static int
yysyntax_error (YYPTRDIFF_T *yymsg_alloc, char **yymsg,
                const yypcontext_t *yyctx)
{
  enum { YYARGS_MAX = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULLPTR;
  /* Arguments of yyformat: reported tokens (one for the "unexpected",
     one per "expected"). */
  yysymbol_kind_t yyarg[YYARGS_MAX];
  /* Cumulated lengths of YYARG.  */
  YYPTRDIFF_T yysize = 0;

  /* Actual size of YYARG. */
  int yycount = yy_syntax_error_arguments (yyctx, yyarg, YYARGS_MAX);
  if (yycount == YYENOMEM)
    return YYENOMEM;

  switch (yycount)
    {
#define YYCASE_(N, S)                       \
      case N:                               \
        yyformat = S;                       \
        break
    default: /* Avoid compiler warnings. */
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
#undef YYCASE_
    }

  /* Compute error message size.  Don't count the "%s"s, but reserve
     room for the terminator.  */
  yysize = yystrlen (yyformat) - 2 * yycount + 1;
  {
    int yyi;
    for (yyi = 0; yyi < yycount; ++yyi)
      {
        YYPTRDIFF_T yysize1
          = yysize + yytnamerr (YY_NULLPTR, yytname[yyarg[yyi]]);
        if (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM)
          yysize = yysize1;
        else
          return YYENOMEM;
      }
  }

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return -1;
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
          yyp += yytnamerr (yyp, yytname[yyarg[yyi++]]);
          yyformat += 2;
        }
      else
        {
          ++yyp;
          ++yyformat;
        }
  }
  return 0;
}


/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg,
            yysymbol_kind_t yykind, YYSTYPE *yyvaluep, void *parm)
{
  YYUSE (yyvaluep);
  YYUSE (parm);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yykind, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YYUSE (yykind);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}






/*----------.
| yyparse.  |
`----------*/

int
yyparse (void *parm)
{
/* Lookahead token kind.  */
int yychar;


/* The semantic value of the lookahead symbol.  */
/* Default value used for initialization, for pacifying older GCCs
   or non-GCC compilers.  */
YY_INITIAL_VALUE (static YYSTYPE yyval_default;)
YYSTYPE yylval YY_INITIAL_VALUE (= yyval_default);

    /* Number of syntax errors so far.  */
    int yynerrs = 0;

    yy_state_fast_t yystate = 0;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus = 0;

    /* Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* Their size.  */
    YYPTRDIFF_T yystacksize = YYINITDEPTH;

    /* The state stack: array, bottom, top.  */
    yy_state_t yyssa[YYINITDEPTH];
    yy_state_t *yyss = yyssa;
    yy_state_t *yyssp = yyss;

    /* The semantic value stack: array, bottom, top.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs = yyvsa;
    YYSTYPE *yyvsp = yyvs;

  int yyn;
  /* The return value of yyparse.  */
  int yyresult;
  /* Lookahead symbol kind.  */
  yysymbol_kind_t yytoken = YYSYMBOL_YYEMPTY;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;

  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYPTRDIFF_T yymsg_alloc = sizeof yymsgbuf;

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yychar = YYEMPTY; /* Cause a token to be read.  */
  goto yysetstate;


/*------------------------------------------------------------.
| yynewstate -- push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;


/*--------------------------------------------------------------------.
| yysetstate -- set current state (the top of the stack) to yystate.  |
`--------------------------------------------------------------------*/
yysetstate:
  YYDPRINTF ((stderr, "Entering state %d\n", yystate));
  YY_ASSERT (0 <= yystate && yystate < YYNSTATES);
  YY_IGNORE_USELESS_CAST_BEGIN
  *yyssp = YY_CAST (yy_state_t, yystate);
  YY_IGNORE_USELESS_CAST_END
  YY_STACK_PRINT (yyss, yyssp);

  if (yyss + yystacksize - 1 <= yyssp)
#if !defined yyoverflow && !defined YYSTACK_RELOCATE
    goto yyexhaustedlab;
#else
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYPTRDIFF_T yysize = yyssp - yyss + 1;

# if defined yyoverflow
      {
        /* Give user a chance to reallocate the stack.  Use copies of
           these so that the &'s don't force the real ones into
           memory.  */
        yy_state_t *yyss1 = yyss;
        YYSTYPE *yyvs1 = yyvs;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * YYSIZEOF (*yyssp),
                    &yyvs1, yysize * YYSIZEOF (*yyvsp),
                    &yystacksize);
        yyss = yyss1;
        yyvs = yyvs1;
      }
# else /* defined YYSTACK_RELOCATE */
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
        goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yy_state_t *yyss1 = yyss;
        union yyalloc *yyptr =
          YY_CAST (union yyalloc *,
                   YYSTACK_ALLOC (YY_CAST (YYSIZE_T, YYSTACK_BYTES (yystacksize))));
        if (! yyptr)
          goto yyexhaustedlab;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
#  undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;

      YY_IGNORE_USELESS_CAST_BEGIN
      YYDPRINTF ((stderr, "Stack size increased to %ld\n",
                  YY_CAST (long, yystacksize)));
      YY_IGNORE_USELESS_CAST_END

      if (yyss + yystacksize - 1 <= yyssp)
        YYABORT;
    }
#endif /* !defined yyoverflow && !defined YYSTACK_RELOCATE */

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

  /* YYCHAR is either empty, or end-of-input, or a valid lookahead.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token\n"));
      yychar = yylex (&yylval, YYLEX_PARAM);
    }

  if (yychar <= YYEOF)
    {
      yychar = YYEOF;
      yytoken = YYSYMBOL_YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else if (yychar == YYerror)
    {
      /* The scanner already issued an error message, process directly
         to error recovery.  But do not keep the error token as
         lookahead, it is too special and may lead us to an endless
         loop in error recovery. */
      yychar = YYUNDEF;
      yytoken = YYSYMBOL_YYerror;
      goto yyerrlab1;
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
  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  /* Discard the shifted token.  */
  yychar = YYEMPTY;
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
| yyreduce -- do a reduction.  |
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
  case 7: /* vardecl_items: %empty  */
        {
#if !EXPOSE_INT_LITS
            initfg(static_cast<ParserState*>(parm));
#endif
        }
    break;

  case 8: /* vardecl_items: vardecl_items_head  */
        {
#if !EXPOSE_INT_LITS
            initfg(static_cast<ParserState*>(parm));
#endif
        }
    break;

  case 11: /* constraint_items: %empty  */
        {
#if EXPOSE_INT_LITS
            initfg(static_cast<ParserState*>(parm));
#endif
        }
    break;

  case 12: /* constraint_items: constraint_items_head  */
        {
#if EXPOSE_INT_LITS
            initfg(static_cast<ParserState*>(parm));
#endif
        }
    break;

  case 33: /* vardecl_item: VAR int_ti_expr_tail ':' ID annotations non_array_expr_opt  */
        {
            ParserState* pp = static_cast<ParserState*>(parm);
            yyassert(pp, !(yyvsp[-4].oSet)() || !(yyvsp[-4].oSet).some()->empty(), "Empty var int domain.");
            bool print = (yyvsp[-1].argVec) && (yyvsp[-1].argVec)->hasAtom("output_var");
            pp->intvarTable.put((yyvsp[-2].sValue), pp->intvars.size());
            if (print) {
                pp->output(std::string((yyvsp[-2].sValue)), new AST::IntVar(pp->intvars.size()));
            }
            bool introduced = (yyvsp[-1].argVec) && (yyvsp[-1].argVec)->hasAtom("var_is_introduced");
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
            delete (yyvsp[-1].argVec);
            free((yyvsp[-2].sValue));
        }
    break;

  case 34: /* vardecl_item: VAR bool_ti_expr_tail ':' ID annotations non_array_expr_opt  */
        {
            ParserState* pp = static_cast<ParserState*>(parm);
            bool print = (yyvsp[-1].argVec) && (yyvsp[-1].argVec)->hasAtom("output_var");
            pp->boolvarTable.put((yyvsp[-2].sValue), pp->boolvars.size());
            if (print) {
                pp->output(std::string((yyvsp[-2].sValue)), new AST::BoolVar(pp->boolvars.size()));
            }
            bool introduced = (yyvsp[-1].argVec) && (yyvsp[-1].argVec)->hasAtom("var_is_introduced");
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
            delete (yyvsp[-1].argVec);
            free((yyvsp[-2].sValue));
        }
    break;

  case 35: /* vardecl_item: VAR float_ti_expr_tail ':' ID annotations non_array_expr_opt  */
        { 
            ParserState* pp = static_cast<ParserState*>(parm);
            yyassert(pp, false, "Floats not supported.");
            delete (yyvsp[-1].argVec);
            free((yyvsp[-2].sValue));
        }
    break;

  case 36: /* vardecl_item: VAR SET OF int_ti_expr_tail ':' ID annotations non_array_expr_opt  */
        { 
            ParserState* pp = static_cast<ParserState*>(parm);
            bool print = (yyvsp[-1].argVec) && (yyvsp[-1].argVec)->hasAtom("output_var");
            pp->setvarTable.put((yyvsp[-2].sValue), pp->setvars.size());
            if (print) {
                pp->output(std::string((yyvsp[-2].sValue)), new AST::SetVar(pp->setvars.size()));
            }
            bool introduced = (yyvsp[-1].argVec) && (yyvsp[-1].argVec)->hasAtom("var_is_introduced");
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
            delete (yyvsp[-1].argVec);
            free((yyvsp[-2].sValue));
        }
    break;

  case 37: /* vardecl_item: int_ti_expr_tail ':' ID annotations '=' non_array_expr  */
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
                    for (unsigned int j = 0; j < sl->s.size(); j++) {
                        if (sl->s[j] == i) {
                            found = true;
                            break;
                        }
                    }
                    yyassert(pp, found, "Empty int domain.");
                }
            }
            pp->intvals.put((yyvsp[-3].sValue), i);
            delete (yyvsp[-2].argVec);
            free((yyvsp[-3].sValue));                
        }
    break;

  case 38: /* vardecl_item: BOOLTOK ':' ID annotations '=' non_array_expr  */
        {
            ParserState* pp = static_cast<ParserState*>(parm);
            yyassert(pp, (yyvsp[0].arg)->isBool(), "Invalid bool initializer.");
            if ((yyvsp[0].arg)->isBool()) {
                pp->boolvals.put((yyvsp[-3].sValue), (yyvsp[0].arg)->getBool());
            }
            delete (yyvsp[-2].argVec);
            free((yyvsp[-3].sValue));                
        }
    break;

  case 39: /* vardecl_item: SET OF int_ti_expr_tail ':' ID annotations '=' non_array_expr  */
        {
            ParserState* pp = static_cast<ParserState*>(parm);
            yyassert(pp, !(yyvsp[-5].oSet)() || !(yyvsp[-5].oSet).some()->empty(), "Empty set domain.");
            yyassert(pp, (yyvsp[0].arg)->isSet(), "Invalid set initializer.");
            AST::SetLit* set = NULL;
            if ((yyvsp[0].arg)->isSet())
                set = (yyvsp[0].arg)->getSet();
            pp->setvals.put((yyvsp[-3].sValue), *set);
            delete set;
            delete (yyvsp[-2].argVec);
            free((yyvsp[-3].sValue));                
        }
    break;

  case 40: /* vardecl_item: ARRAY '[' INT_LIT DOTDOT INT_LIT ']' OF VAR int_ti_expr_tail ':' ID annotations vardecl_int_var_array_init  */
        {
            ParserState* pp = static_cast<ParserState*>(parm);
            yyassert(pp, (yyvsp[-10].iValue) == 1, "Arrays must start at 1");
            if (!pp->hadError) {
                bool print = (yyvsp[-1].argVec) && (yyvsp[-1].argVec)->hasCall("output_array");
                vector<int> vars((yyvsp[-8].iValue));
                yyassert(pp, !(yyvsp[-4].oSet)() || !(yyvsp[-4].oSet).some()->empty(), "Empty var int domain.");
                if (!pp->hadError) {
                    if ((yyvsp[0].oVarSpecVec)()) {
                        vector<VarSpec*>* vsv = (yyvsp[0].oVarSpecVec).some();
                        yyassert(pp, vsv->size() == static_cast<unsigned int>((yyvsp[-8].iValue)),
                            "Initializer size does not match array dimension");
                        if (!pp->hadError) {
                            for (int i = 0; i < (yyvsp[-8].iValue); i++) {
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
                                    addDomainConstraint(pp, "set_in", new AST::IntVar(vars[i]), opt);
                                }
                            }
                        }
                        delete vsv;
                    } else {
                        IntVarSpec* ispec = new IntVarSpec((yyvsp[-4].oSet),print,!print,false);
                        string arrayname = "["; arrayname += (yyvsp[-2].sValue);
                        for (int i = 0; i < (yyvsp[-8].iValue)-1; i++) {
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
                    for (int i = 0; i < (yyvsp[-8].iValue); i++)
                        output->a.push_back(new AST::IntVar(vars[i]));
                    a->a.push_back(output);
                    a->a.push_back(new AST::String(")"));
                    pp->output(std::string((yyvsp[-2].sValue)), a);
                }
                pp->intvararrays.put((yyvsp[-2].sValue), vars);
            }
            delete (yyvsp[-1].argVec);
            free((yyvsp[-2].sValue));
        }
    break;

  case 41: /* vardecl_item: ARRAY '[' INT_LIT DOTDOT INT_LIT ']' OF VAR bool_ti_expr_tail ':' ID annotations vardecl_bool_var_array_init  */
        {
            ParserState* pp = static_cast<ParserState*>(parm);
            bool print = (yyvsp[-1].argVec) && (yyvsp[-1].argVec)->hasCall("output_array");
            yyassert(pp, (yyvsp[-10].iValue) == 1, "Arrays must start at 1");
            if (!pp->hadError) {
                vector<int> vars((yyvsp[-8].iValue));
                if ((yyvsp[0].oVarSpecVec)()) {
                    vector<VarSpec*>* vsv = (yyvsp[0].oVarSpecVec).some();
                    yyassert(pp, vsv->size() == static_cast<unsigned int>((yyvsp[-8].iValue)),
                        "Initializer size does not match array dimension");
                    if (!pp->hadError) {
                        for (int i = 0; i < (yyvsp[-8].iValue); i++) {
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
                                addDomainConstraint(pp, "set_in", new AST::BoolVar(vars[i]), opt);
                            }
                        }
                    }
                    delete vsv;
                } else {
                    for (int i = 0; i < (yyvsp[-8].iValue); i++) {
                        vars[i] = pp->boolvars.size();
                        pp->boolvars.push_back(varspec((yyvsp[-2].sValue),
                            new BoolVarSpec((yyvsp[-4].oSet),print,!print,false)));
                    }                    
                }
                if (print) {
                    AST::Array* a = new AST::Array();
                    a->a.push_back(arrayOutput((yyvsp[-1].argVec)->getCall("output_array")));
                    AST::Array* output = new AST::Array();
                    for (int i = 0; i < (yyvsp[-8].iValue); i++)
                        output->a.push_back(new AST::BoolVar(vars[i]));
                    a->a.push_back(output);
                    a->a.push_back(new AST::String(")"));
                    pp->output(std::string((yyvsp[-2].sValue)), a);
                }
                pp->boolvararrays.put((yyvsp[-2].sValue), vars);
            }
            delete (yyvsp[-1].argVec);
            free((yyvsp[-2].sValue));
        }
    break;

  case 42: /* vardecl_item: ARRAY '[' INT_LIT DOTDOT INT_LIT ']' OF VAR float_ti_expr_tail ':' ID annotations vardecl_float_var_array_init  */
        { 
            ParserState* pp = static_cast<ParserState*>(parm);
            yyassert(pp, false, "Floats not supported.");
            delete (yyvsp[-1].argVec);
            free((yyvsp[-2].sValue));
        }
    break;

  case 43: /* vardecl_item: ARRAY '[' INT_LIT DOTDOT INT_LIT ']' OF VAR SET OF int_ti_expr_tail ':' ID annotations vardecl_set_var_array_init  */
        { 
            ParserState* pp = static_cast<ParserState*>(parm);
            bool print = (yyvsp[-1].argVec) && (yyvsp[-1].argVec)->hasCall("output_array");
            yyassert(pp, (yyvsp[-12].iValue) == 1, "Arrays must start at 1");
            if (!pp->hadError) {
                vector<int> vars((yyvsp[-10].iValue));
                if ((yyvsp[0].oVarSpecVec)()) {
                    vector<VarSpec*>* vsv = (yyvsp[0].oVarSpecVec).some();
                    yyassert(pp, vsv->size() == static_cast<unsigned int>((yyvsp[-10].iValue)),
                        "Initializer size does not match array dimension");
                    if (!pp->hadError) {
                        for (int i = 0; i < (yyvsp[-10].iValue); i++) {
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
                                addDomainConstraint(pp, "set_subset", new AST::SetVar(vars[i]), opt);
                            }
                        }
                    }
                    delete vsv;
                } else {
                    SetVarSpec* ispec = new SetVarSpec((yyvsp[-4].oSet),print,!print, false);
                    string arrayname = "["; arrayname += (yyvsp[-2].sValue);
                    for (int i = 0; i < (yyvsp[-10].iValue)-1; i++) {
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
                    for (int i = 0; i < (yyvsp[-10].iValue); i++)
                        output->a.push_back(new AST::SetVar(vars[i]));
                    a->a.push_back(output);
                    a->a.push_back(new AST::String(")"));
                    pp->output(std::string((yyvsp[-2].sValue)), a);
                }
                pp->setvararrays.put((yyvsp[-2].sValue), vars);
            }
            delete (yyvsp[-1].argVec);
            free((yyvsp[-2].sValue));
        }
    break;

  case 44: /* vardecl_item: ARRAY '[' INT_LIT DOTDOT INT_LIT ']' OF int_ti_expr_tail ':' ID annotations '=' '[' int_list ']'  */
        {
            ParserState* pp = static_cast<ParserState*>(parm);
            yyassert(pp, (yyvsp[-12].iValue) == 1, "Arrays must start at 1");
            yyassert(pp, (yyvsp[-1].setValue)->size() == static_cast<unsigned int>((yyvsp[-10].iValue)),
                             "Initializer size does not match array dimension");
            if (!pp->hadError)
                pp->intvalarrays.put((yyvsp[-5].sValue), *(yyvsp[-1].setValue));
            delete (yyvsp[-1].setValue);
            free((yyvsp[-5].sValue));
            delete (yyvsp[-4].argVec);
        }
    break;

  case 45: /* vardecl_item: ARRAY '[' INT_LIT DOTDOT INT_LIT ']' OF BOOLTOK ':' ID annotations '=' '[' bool_list ']'  */
        {
            ParserState* pp = static_cast<ParserState*>(parm);
            yyassert(pp, (yyvsp[-12].iValue) == 1, "Arrays must start at 1");
            yyassert(pp, (yyvsp[-1].setValue)->size() == static_cast<unsigned int>((yyvsp[-10].iValue)),
                             "Initializer size does not match array dimension");
            if (!pp->hadError)
                pp->boolvalarrays.put((yyvsp[-5].sValue), *(yyvsp[-1].setValue));
            delete (yyvsp[-1].setValue);
            free((yyvsp[-5].sValue));
            delete (yyvsp[-4].argVec);
        }
    break;

  case 46: /* vardecl_item: ARRAY '[' INT_LIT DOTDOT INT_LIT ']' OF FLOATTOK ':' ID annotations '=' '[' float_list ']'  */
        {
            ParserState* pp = static_cast<ParserState*>(parm);
            yyassert(pp, false, "Floats not supported.");
            delete (yyvsp[-4].argVec);
            free((yyvsp[-5].sValue));
        }
    break;

  case 47: /* vardecl_item: ARRAY '[' INT_LIT DOTDOT INT_LIT ']' OF SET OF int_ti_expr_tail ':' ID annotations '=' '[' set_literal_list ']'  */
        {
            ParserState* pp = static_cast<ParserState*>(parm);
            yyassert(pp, (yyvsp[-14].iValue) == 1, "Arrays must start at 1");
            yyassert(pp, (yyvsp[-1].setValueList)->size() == static_cast<unsigned int>((yyvsp[-12].iValue)),
                             "Initializer size does not match array dimension");
            if (!pp->hadError)
                pp->setvalarrays.put((yyvsp[-5].sValue), *(yyvsp[-1].setValueList));
            delete (yyvsp[-1].setValueList);
            delete (yyvsp[-4].argVec);
            free((yyvsp[-5].sValue));
        }
    break;

  case 48: /* int_init: INT_LIT  */
        { 
            (yyval.varSpec) = new IntVarSpec((yyvsp[0].iValue), false, true, false);
        }
    break;

  case 49: /* int_init: ID  */
        { 
            int v = 0;
            ParserState* pp = static_cast<ParserState*>(parm);
            if (pp->intvarTable.get((yyvsp[0].sValue), v))
                (yyval.varSpec) = new IntVarSpec(Alias(v), false, true, false);
            else {
                pp->err << "Error: undefined identifier " << (yyvsp[0].sValue)
                        << " in line no. "
                        << yyget_lineno(pp->yyscanner) << std::endl;
                pp->hadError = true;
                (yyval.varSpec) = new IntVarSpec(0,false,true,false); // keep things consistent
            }
            free((yyvsp[0].sValue));
        }
    break;

  case 50: /* int_init: ID '[' INT_LIT ']'  */
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
    break;

  case 51: /* int_init_list: %empty  */
        { 
            (yyval.varSpecVec) = new vector<VarSpec*>(0); 
        }
    break;

  case 52: /* int_init_list: int_init_list_head list_tail  */
        { 
            (yyval.varSpecVec) = (yyvsp[-1].varSpecVec); 
        }
    break;

  case 53: /* int_init_list_head: int_init  */
        { 
            (yyval.varSpecVec) = new vector<VarSpec*>(1); 
            (*(yyval.varSpecVec))[0] = (yyvsp[0].varSpec); 
        }
    break;

  case 54: /* int_init_list_head: int_init_list_head ',' int_init  */
        { 
            (yyval.varSpecVec) = (yyvsp[-2].varSpecVec); 
            (yyval.varSpecVec)->push_back((yyvsp[0].varSpec)); 
        }
    break;

  case 57: /* int_var_array_literal: '[' int_init_list ']'  */
        { 
            (yyval.varSpecVec) = (yyvsp[-1].varSpecVec); 
        }
    break;

  case 58: /* float_init: FLOAT_LIT  */
        { 
            (yyval.varSpec) = new FloatVarSpec((yyvsp[0].dValue),false,true,false); 
        }
    break;

  case 59: /* float_init: ID  */
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
    break;

  case 60: /* float_init: ID '[' INT_LIT ']'  */
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
    break;

  case 61: /* float_init_list: %empty  */
        { 
            (yyval.varSpecVec) = new vector<VarSpec*>(0); 
        }
    break;

  case 62: /* float_init_list: float_init_list_head list_tail  */
        { 
            (yyval.varSpecVec) = (yyvsp[-1].varSpecVec); 
        }
    break;

  case 63: /* float_init_list_head: float_init  */
        {   
            (yyval.varSpecVec) = new vector<VarSpec*>(1); 
            (*(yyval.varSpecVec))[0] = (yyvsp[0].varSpec); 
        }
    break;

  case 64: /* float_init_list_head: float_init_list_head ',' float_init  */
        { 
            (yyval.varSpecVec) = (yyvsp[-2].varSpecVec); 
            (yyval.varSpecVec)->push_back((yyvsp[0].varSpec)); 
        }
    break;

  case 65: /* float_var_array_literal: '[' float_init_list ']'  */
        { 
            (yyval.varSpecVec) = (yyvsp[-1].varSpecVec); 
        }
    break;

  case 66: /* bool_init: BOOL_LIT  */
        { 
            (yyval.varSpec) = new BoolVarSpec((yyvsp[0].iValue),false,true,false); 
        }
    break;

  case 67: /* bool_init: ID  */
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
    break;

  case 68: /* bool_init: ID '[' INT_LIT ']'  */
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
    break;

  case 69: /* bool_init_list: %empty  */
        { 
            (yyval.varSpecVec) = new vector<VarSpec*>(0); 
        }
    break;

  case 70: /* bool_init_list: bool_init_list_head list_tail  */
        { 
            (yyval.varSpecVec) = (yyvsp[-1].varSpecVec); 
        }
    break;

  case 71: /* bool_init_list_head: bool_init  */
        { 
            (yyval.varSpecVec) = new vector<VarSpec*>(1); 
            (*(yyval.varSpecVec))[0] = (yyvsp[0].varSpec); 
        }
    break;

  case 72: /* bool_init_list_head: bool_init_list_head ',' bool_init  */
        { 
            (yyval.varSpecVec) = (yyvsp[-2].varSpecVec); 
            (yyval.varSpecVec)->push_back((yyvsp[0].varSpec)); 
        }
    break;

  case 73: /* bool_var_array_literal: '[' bool_init_list ']'  */
                               { (yyval.varSpecVec) = (yyvsp[-1].varSpecVec); }
    break;

  case 74: /* set_init: set_literal  */
        { 
            (yyval.varSpec) = new SetVarSpec(Option<AST::SetLit*>::some((yyvsp[0].setLit)),false,true,false); 
        }
    break;

  case 75: /* set_init: ID  */
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
    break;

  case 76: /* set_init: ID '[' INT_LIT ']'  */
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
    break;

  case 77: /* set_init_list: %empty  */
        { 
            (yyval.varSpecVec) = new vector<VarSpec*>(0); 
        }
    break;

  case 78: /* set_init_list: set_init_list_head list_tail  */
        { 
            (yyval.varSpecVec) = (yyvsp[-1].varSpecVec); 
        }
    break;

  case 79: /* set_init_list_head: set_init  */
        { 
            (yyval.varSpecVec) = new vector<VarSpec*>(1); 
            (*(yyval.varSpecVec))[0] = (yyvsp[0].varSpec); 
        }
    break;

  case 80: /* set_init_list_head: set_init_list_head ',' set_init  */
        { 
            (yyval.varSpecVec) = (yyvsp[-2].varSpecVec); 
            (yyval.varSpecVec)->push_back((yyvsp[0].varSpec)); 
        }
    break;

  case 81: /* set_var_array_literal: '[' set_init_list ']'  */
        { 
            (yyval.varSpecVec) = (yyvsp[-1].varSpecVec); 
        }
    break;

  case 82: /* vardecl_int_var_array_init: %empty  */
        { 
            (yyval.oVarSpecVec) = Option<vector<VarSpec*>* >::none(); 
        }
    break;

  case 83: /* vardecl_int_var_array_init: '=' int_var_array_literal  */
        { 
            (yyval.oVarSpecVec) = Option<vector<VarSpec*>* >::some((yyvsp[0].varSpecVec)); 
        }
    break;

  case 84: /* vardecl_bool_var_array_init: %empty  */
        { 
            (yyval.oVarSpecVec) = Option<vector<VarSpec*>* >::none(); 
        }
    break;

  case 85: /* vardecl_bool_var_array_init: '=' bool_var_array_literal  */
        { 
            (yyval.oVarSpecVec) = Option<vector<VarSpec*>* >::some((yyvsp[0].varSpecVec)); 
        }
    break;

  case 86: /* vardecl_float_var_array_init: %empty  */
        { 
            (yyval.oVarSpecVec) = Option<vector<VarSpec*>* >::none(); 
        }
    break;

  case 87: /* vardecl_float_var_array_init: '=' float_var_array_literal  */
        { 
            (yyval.oVarSpecVec) = Option<vector<VarSpec*>* >::some((yyvsp[0].varSpecVec)); 
        }
    break;

  case 88: /* vardecl_set_var_array_init: %empty  */
        { 
            (yyval.oVarSpecVec) = Option<vector<VarSpec*>* >::none(); 
        }
    break;

  case 89: /* vardecl_set_var_array_init: '=' set_var_array_literal  */
        { 
            (yyval.oVarSpecVec) = Option<vector<VarSpec*>* >::some((yyvsp[0].varSpecVec)); 
        }
    break;

  case 90: /* constraint_item: CONSTRAINT ID '(' flat_expr_list ')' annotations  */
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
    break;

  case 91: /* constraint_item: CONSTRAINT ID annotations  */
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
    break;

  case 92: /* constraint_item: CONSTRAINT ID '[' INT_LIT ']' annotations  */
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
    break;

  case 93: /* solve_item: SOLVE annotations SATISFY  */
        { 
            ParserState *pp = static_cast<ParserState*>(parm);
            if (!pp->hadError) {
                pp->fg->solve((yyvsp[-1].argVec));
            }
            delete (yyvsp[-1].argVec);
        }
    break;

  case 94: /* solve_item: SOLVE annotations minmax solve_expr  */
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
    break;

  case 95: /* int_ti_expr_tail: INTTOK  */
        { 
            (yyval.oSet) = Option<AST::SetLit* >::none(); 
        }
    break;

  case 96: /* int_ti_expr_tail: '{' int_list '}'  */
        { 
            (yyval.oSet) = Option<AST::SetLit* >::some(new AST::SetLit(*(yyvsp[-1].setValue))); 
        }
    break;

  case 97: /* int_ti_expr_tail: INT_LIT DOTDOT INT_LIT  */
        { 
            (yyval.oSet) = Option<AST::SetLit* >::some(new AST::SetLit((yyvsp[-2].iValue), (yyvsp[0].iValue)));
        }
    break;

  case 98: /* bool_ti_expr_tail: BOOLTOK  */
        { 
            (yyval.oSet) = Option<AST::SetLit* >::none(); 
        }
    break;

  case 99: /* bool_ti_expr_tail: '{' bool_list_head list_tail '}'  */
        { 
            bool haveTrue = false;
            bool haveFalse = false;
            for (int i = (yyvsp[-2].setValue)->size(); i--;) {
                haveTrue |= ((*(yyvsp[-2].setValue))[i] == 1);
                haveFalse |= ((*(yyvsp[-2].setValue))[i] == 0);
            }
            delete (yyvsp[-2].setValue);
            (yyval.oSet) = Option<AST::SetLit* >::some(
                new AST::SetLit(!haveFalse,haveTrue));
        }
    break;

  case 102: /* set_literal: '{' int_list '}'  */
        { 
            (yyval.setLit) = new AST::SetLit(*(yyvsp[-1].setValue)); 
        }
    break;

  case 103: /* set_literal: INT_LIT DOTDOT INT_LIT  */
        { 
            (yyval.setLit) = new AST::SetLit((yyvsp[-2].iValue), (yyvsp[0].iValue)); 
        }
    break;

  case 104: /* int_list: %empty  */
        { 
            (yyval.setValue) = new vector<int>(0); 
        }
    break;

  case 105: /* int_list: int_list_head list_tail  */
        { 
            (yyval.setValue) = (yyvsp[-1].setValue); 
        }
    break;

  case 106: /* int_list_head: INT_LIT  */
        { 
            (yyval.setValue) = new vector<int>(1); 
            (*(yyval.setValue))[0] = (yyvsp[0].iValue); 
        }
    break;

  case 107: /* int_list_head: int_list_head ',' INT_LIT  */
        { 
            (yyval.setValue) = (yyvsp[-2].setValue); 
            (yyval.setValue)->push_back((yyvsp[0].iValue)); 
        }
    break;

  case 108: /* bool_list: %empty  */
        { 
            (yyval.setValue) = new vector<int>(0); 
        }
    break;

  case 109: /* bool_list: bool_list_head list_tail  */
        { 
            (yyval.setValue) = (yyvsp[-1].setValue); 
        }
    break;

  case 110: /* bool_list_head: BOOL_LIT  */
        { 
            (yyval.setValue) = new vector<int>(1); 
            (*(yyval.setValue))[0] = (yyvsp[0].iValue); 
        }
    break;

  case 111: /* bool_list_head: bool_list_head ',' BOOL_LIT  */
        { 
            (yyval.setValue) = (yyvsp[-2].setValue); 
            (yyval.setValue)->push_back((yyvsp[0].iValue)); 
        }
    break;

  case 112: /* float_list: %empty  */
        { 
            (yyval.floatSetValue) = new vector<double>(0); 
        }
    break;

  case 113: /* float_list: float_list_head list_tail  */
        { 
            (yyval.floatSetValue) = (yyvsp[-1].floatSetValue); 
        }
    break;

  case 114: /* float_list_head: FLOAT_LIT  */
        {
            (yyval.floatSetValue) = new vector<double>(1); 
            (*(yyval.floatSetValue))[0] = (yyvsp[0].dValue); 
        }
    break;

  case 115: /* float_list_head: float_list_head ',' FLOAT_LIT  */
        { 
            (yyval.floatSetValue) = (yyvsp[-2].floatSetValue); 
            (yyval.floatSetValue)->push_back((yyvsp[0].dValue)); 
        }
    break;

  case 116: /* set_literal_list: %empty  */
        { 
            (yyval.setValueList) = new vector<AST::SetLit>(0); 
        }
    break;

  case 117: /* set_literal_list: set_literal_list_head list_tail  */
        { 
            (yyval.setValueList) = (yyvsp[-1].setValueList); 
        }
    break;

  case 118: /* set_literal_list_head: set_literal  */
        { 
            (yyval.setValueList) = new vector<AST::SetLit>(1); 
            (*(yyval.setValueList))[0] = *(yyvsp[0].setLit); 
            delete (yyvsp[0].setLit); 
        }
    break;

  case 119: /* set_literal_list_head: set_literal_list_head ',' set_literal  */
        { 
            (yyval.setValueList) = (yyvsp[-2].setValueList); 
            (yyval.setValueList)->push_back(*(yyvsp[0].setLit)); 
            delete (yyvsp[0].setLit); 
        }
    break;

  case 120: /* flat_expr_list: flat_expr  */
        { 
            (yyval.argVec) = new AST::Array((yyvsp[0].arg)); 
        }
    break;

  case 121: /* flat_expr_list: flat_expr_list ',' flat_expr  */
        { 
            (yyval.argVec) = (yyvsp[-2].argVec); 
            (yyval.argVec)->append((yyvsp[0].arg)); 
        }
    break;

  case 122: /* flat_expr: non_array_expr  */
        { 
            (yyval.arg) = (yyvsp[0].arg); 
        }
    break;

  case 123: /* flat_expr: '[' non_array_expr_list ']'  */
        { 
            (yyval.arg) = (yyvsp[-1].argVec); 
        }
    break;

  case 124: /* non_array_expr_opt: %empty  */
        { 
            (yyval.oArg) = Option<AST::Node*>::none(); 
        }
    break;

  case 125: /* non_array_expr_opt: '=' non_array_expr  */
        { 
            (yyval.oArg) = Option<AST::Node*>::some((yyvsp[0].arg)); 
        }
    break;

  case 126: /* non_array_expr: BOOL_LIT  */
        { 
            (yyval.arg) = new AST::BoolLit((yyvsp[0].iValue)); 
        }
    break;

  case 127: /* non_array_expr: INT_LIT  */
        { 
            (yyval.arg) = new AST::IntLit((yyvsp[0].iValue)); 
        }
    break;

  case 128: /* non_array_expr: FLOAT_LIT  */
        { 
            (yyval.arg) = new AST::FloatLit((yyvsp[0].dValue)); 
        }
    break;

  case 129: /* non_array_expr: set_literal  */
        { 
            (yyval.arg) = (yyvsp[0].setLit); 
        }
    break;

  case 130: /* non_array_expr: ID  */
        { 
            vector<int> as;
            ParserState* pp = static_cast<ParserState*>(parm);
            if (pp->intvararrays.get((yyvsp[0].sValue), as)) {
                AST::Array *ia = new AST::Array(as.size());
                for (int i = as.size(); i--;)
                    ia->a[i] = new AST::IntVar(as[i]);
                (yyval.arg) = ia;
            } else if (pp->boolvararrays.get((yyvsp[0].sValue), as)) {
                AST::Array *ia = new AST::Array(as.size());
                for (int i = as.size(); i--;)
                    ia->a[i] = new AST::BoolVar(as[i]);
                (yyval.arg) = ia;
            } else if (pp->setvararrays.get((yyvsp[0].sValue), as)) {
                AST::Array *ia = new AST::Array(as.size());
                for (int i = as.size(); i--;)
                    ia->a[i] = new AST::SetVar(as[i]);
                (yyval.arg) = ia;
            } else {
                std::vector<int> is;
                std::vector<AST::SetLit> isS;
                int ival = 0;
                bool bval = false;
                if (pp->intvalarrays.get((yyvsp[0].sValue), is)) {
                    AST::Array *v = new AST::Array(is.size());
                    for (int i = is.size(); i--;)
                        v->a[i] = new AST::IntLit(is[i]);
                    (yyval.arg) = v;
                } else if (pp->boolvalarrays.get((yyvsp[0].sValue), is)) {
                    AST::Array *v = new AST::Array(is.size());
                    for (int i = is.size(); i--;)
                        v->a[i] = new AST::BoolLit(is[i]);
                    (yyval.arg) = v;
                } else if (pp->setvalarrays.get((yyvsp[0].sValue), isS)) {
                    AST::Array *v = new AST::Array(isS.size());
                    for (int i = isS.size(); i--;)
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
    break;

  case 131: /* non_array_expr: ID '[' non_array_expr ']'  */
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
    break;

  case 132: /* non_array_expr_list: %empty  */
        { 
            (yyval.argVec) = new AST::Array(0); 
        }
    break;

  case 133: /* non_array_expr_list: non_array_expr_list_head list_tail  */
        { 
            (yyval.argVec) = (yyvsp[-1].argVec); 
        }
    break;

  case 134: /* non_array_expr_list_head: non_array_expr  */
        { 
            (yyval.argVec) = new AST::Array((yyvsp[0].arg)); 
        }
    break;

  case 135: /* non_array_expr_list_head: non_array_expr_list_head ',' non_array_expr  */
        { 
            (yyval.argVec) = (yyvsp[-2].argVec); 
            (yyval.argVec)->append((yyvsp[0].arg)); 
        }
    break;

  case 136: /* solve_expr: INT_LIT  */
        {
            ParserState *pp = static_cast<ParserState*>(parm);
            // Create a new variable in the parser and append at the end
            const int i = pp->intvars.size();
            const std::string objname = "X_INTRODUCED_CHUFFEDOBJ";
            pp->intvarTable.put(objname, i);
            pp->intvars.push_back(varspec(objname,
                new IntVarSpec((yyvsp[0].iValue),false,true,false)));
            if (pp->fg != NULL) {
                // Add a new IntVar to the FlatZincSpace if it was already created
                try {
                    pp->fg->newIntVar(static_cast<IntVarSpec*>(pp->intvars[i].second));
                    IntVar* newiv = pp->fg->iv[pp->fg->intVarCount-1];
                    intVarString.insert(std::pair<IntVar*, std::string>(newiv, pp->intvars[i].first));
                } catch (FlatZinc::Error& e) {
                    yyerror(pp, e.toString().c_str());
                }
            }
            (yyval.iValue) = i;
        }
    break;

  case 137: /* solve_expr: ID  */
        { 
            ParserState *pp = static_cast<ParserState*>(parm);
            int tmp = -1;
            // Check whether the Objective variable is an integer constant
            if (pp->intvals.get((yyvsp[0].sValue), tmp) && !pp->intvarTable.get((yyvsp[0].sValue), (yyval.iValue))) {
                // Create a new variable in the parser and append at the end
                const int i = pp->intvars.size();
                pp->intvarTable.put((yyvsp[0].sValue), i);
                pp->intvars.push_back(varspec((yyvsp[0].sValue),
                    new IntVarSpec(tmp,false,true,false)));
                if (pp->fg != NULL) {
                    // Add a new IntVar to the FlatZincSpace if it was already created
                    try {
                        pp->fg->newIntVar(static_cast<IntVarSpec*>(pp->intvars[i].second));
                        IntVar* newiv = pp->fg->iv[pp->fg->intVarCount-1];
                        intVarString.insert(std::pair<IntVar*, std::string>(newiv, pp->intvars[i].first));
                    } catch (FlatZinc::Error& e) {
                        yyerror(pp, e.toString().c_str());
                    }
                }
            }
            if (!pp->intvarTable.get((yyvsp[0].sValue), (yyval.iValue))) {
                pp->err << "Error: unknown integer variable " << (yyvsp[0].sValue)
                        << " in line no. "
                        << yyget_lineno(pp->yyscanner) << std::endl;
                pp->hadError = true;
            }
            free((yyvsp[0].sValue));
        }
    break;

  case 138: /* solve_expr: ID '[' INT_LIT ']'  */
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
    break;

  case 141: /* annotations: %empty  */
        { 
            (yyval.argVec) = NULL; 
        }
    break;

  case 142: /* annotations: annotations_head  */
        { 
            (yyval.argVec) = (yyvsp[0].argVec); 
        }
    break;

  case 143: /* annotations_head: COLONCOLON annotation  */
        { 
            (yyval.argVec) = new AST::Array((yyvsp[0].arg)); 
        }
    break;

  case 144: /* annotations_head: annotations_head COLONCOLON annotation  */
        { 
            (yyval.argVec) = (yyvsp[-2].argVec); 
            (yyval.argVec)->append((yyvsp[0].arg)); 
        }
    break;

  case 145: /* annotation: ID '(' annotation_list ')'  */
        { 
            (yyval.arg) = new AST::Call((yyvsp[-3].sValue), AST::extractSingleton((yyvsp[-1].arg))); 
            free((yyvsp[-3].sValue));
        }
    break;

  case 146: /* annotation: annotation_expr  */
        { 
            (yyval.arg) = (yyvsp[0].arg); 
        }
    break;

  case 147: /* annotation_list: annotation  */
        { 
            (yyval.arg) = new AST::Array((yyvsp[0].arg)); 
        }
    break;

  case 148: /* annotation_list: annotation_list ',' annotation  */
        { 
            (yyval.arg) = (yyvsp[-2].arg); 
            (yyval.arg)->append((yyvsp[0].arg)); 
        }
    break;

  case 149: /* annotation_expr: ann_non_array_expr  */
        { 
            (yyval.arg) = (yyvsp[0].arg); 
        }
    break;

  case 150: /* annotation_expr: '[' annotation_list ']'  */
        { 
            (yyval.arg) = (yyvsp[-1].arg); 
        }
    break;

  case 151: /* ann_non_array_expr: BOOL_LIT  */
        { 
            (yyval.arg) = new AST::BoolLit((yyvsp[0].iValue)); 
        }
    break;

  case 152: /* ann_non_array_expr: INT_LIT  */
        { 
            (yyval.arg) = new AST::IntLit((yyvsp[0].iValue)); 
        }
    break;

  case 153: /* ann_non_array_expr: FLOAT_LIT  */
        { 
            (yyval.arg) = new AST::FloatLit((yyvsp[0].dValue)); 
        }
    break;

  case 154: /* ann_non_array_expr: set_literal  */
        { 
            (yyval.arg) = (yyvsp[0].setLit); 
        }
    break;

  case 155: /* ann_non_array_expr: ID  */
        { 
            vector<int> as;
            ParserState* pp = static_cast<ParserState*>(parm);
            if (pp->intvararrays.get((yyvsp[0].sValue), as)) {
                AST::Array *ia = new AST::Array(as.size());
                for (int i = as.size(); i--;)
                    ia->a[i] = new AST::IntVar(as[i]);
                (yyval.arg) = ia;
            } else if (pp->boolvararrays.get((yyvsp[0].sValue), as)) {
                AST::Array *ia = new AST::Array(as.size());
                for (int i = as.size(); i--;)
                    ia->a[i] = new AST::BoolVar(as[i]);
                (yyval.arg) = ia;
            } else if (pp->setvararrays.get((yyvsp[0].sValue), as)) {
                AST::Array *ia = new AST::Array(as.size());
                for (int i = as.size(); i--;)
                    ia->a[i] = new AST::SetVar(as[i]);
                (yyval.arg) = ia;
            } else {
                std::vector<int> is;
                int ival = 0;
                bool bval = false;
                if (pp->intvalarrays.get((yyvsp[0].sValue), is)) {
                    AST::Array *v = new AST::Array(is.size());
                    for (int i = is.size(); i--;)
                        v->a[i] = new AST::IntLit(is[i]);
                    (yyval.arg) = v;
                } else if (pp->boolvalarrays.get((yyvsp[0].sValue), is)) {
                    AST::Array *v = new AST::Array(is.size());
                    for (int i = is.size(); i--;)
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
    break;

  case 156: /* ann_non_array_expr: ID '[' ann_non_array_expr ']'  */
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
    break;

  case 157: /* ann_non_array_expr: STRING_LIT  */
        {
            (yyval.arg) = new AST::String((yyvsp[0].sValue));
            free((yyvsp[0].sValue));
        }
    break;



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
  YY_SYMBOL_PRINT ("-> $$ =", YY_CAST (yysymbol_kind_t, yyr1[yyn]), &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;

  *++yyvsp = yyval;

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */
  {
    const int yylhs = yyr1[yyn] - YYNTOKENS;
    const int yyi = yypgoto[yylhs] + *yyssp;
    yystate = (0 <= yyi && yyi <= YYLAST && yycheck[yyi] == *yyssp
               ? yytable[yyi]
               : yydefgoto[yylhs]);
  }

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYSYMBOL_YYEMPTY : YYTRANSLATE (yychar);
  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
      {
        yypcontext_t yyctx
          = {yyssp, yytoken};
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        yysyntax_error_status = yysyntax_error (&yymsg_alloc, &yymsg, &yyctx);
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == -1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = YY_CAST (char *,
                             YYSTACK_ALLOC (YY_CAST (YYSIZE_T, yymsg_alloc)));
            if (yymsg)
              {
                yysyntax_error_status
                  = yysyntax_error (&yymsg_alloc, &yymsg, &yyctx);
                yymsgp = yymsg;
              }
            else
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = YYENOMEM;
              }
          }
        yyerror (parm, yymsgp);
        if (yysyntax_error_status == YYENOMEM)
          goto yyexhaustedlab;
      }
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
  /* Pacify compilers when the user code never invokes YYERROR and the
     label yyerrorlab therefore never appears in user code.  */
  if (0)
    YYERROR;

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

  /* Pop stack until we find a state that shifts the error token.  */
  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYSYMBOL_YYerror;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYSYMBOL_YYerror)
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
                  YY_ACCESSING_SYMBOL (yystate), yyvsp, parm);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", YY_ACCESSING_SYMBOL (yyn), yyvsp, yylsp);

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


#if 1
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (parm, YY_("memory exhausted"));
  yyresult = 2;
  goto yyreturn;
#endif


/*-------------------------------------------------------.
| yyreturn -- parsing is finished, clean up and return.  |
`-------------------------------------------------------*/
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
                  YY_ACCESSING_SYMBOL (+*yyssp), yyvsp, parm);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
  return yyresult;
}


/* A Bison parser, made by GNU Bison 3.6.4.  */

/* Bison interface for Yacc-like parsers in C

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

/* DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
   especially those whose name start with YY_ or yy_.  They are
   private implementation details that can be changed or removed.  */

#ifndef YY_YY_USERS_JDEK0001_DROPBOX_DEVELOPMENT_CHUFFED_BUILD_CHUFFED_FLATZINC_PARSER_TAB_H_INCLUDED
# define YY_YY_USERS_JDEK0001_DROPBOX_DEVELOPMENT_CHUFFED_BUILD_CHUFFED_FLATZINC_PARSER_TAB_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int yydebug;
#endif

/* Token kinds.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    YYEMPTY = -2,
    YYEOF = 0,                     /* "end of file"  */
    YYerror = 256,                 /* error  */
    YYUNDEF = 257,                 /* "invalid token"  */
    INT_LIT = 258,                 /* INT_LIT  */
    BOOL_LIT = 259,                /* BOOL_LIT  */
    FLOAT_LIT = 260,               /* FLOAT_LIT  */
    ID = 261,                      /* ID  */
    STRING_LIT = 262,              /* STRING_LIT  */
    VAR = 263,                     /* VAR  */
    PAR = 264,                     /* PAR  */
    ANNOTATION = 265,              /* ANNOTATION  */
    ANY = 266,                     /* ANY  */
    ARRAY = 267,                   /* ARRAY  */
    BOOLTOK = 268,                 /* BOOLTOK  */
    CASE = 269,                    /* CASE  */
    COLONCOLON = 270,              /* COLONCOLON  */
    CONSTRAINT = 271,              /* CONSTRAINT  */
    DEFAULT = 272,                 /* DEFAULT  */
    DOTDOT = 273,                  /* DOTDOT  */
    ELSE = 274,                    /* ELSE  */
    ELSEIF = 275,                  /* ELSEIF  */
    ENDIF = 276,                   /* ENDIF  */
    ENUM = 277,                    /* ENUM  */
    FLOATTOK = 278,                /* FLOATTOK  */
    FUNCTION = 279,                /* FUNCTION  */
    IF = 280,                      /* IF  */
    INCLUDE = 281,                 /* INCLUDE  */
    INTTOK = 282,                  /* INTTOK  */
    LET = 283,                     /* LET  */
    MAXIMIZE = 284,                /* MAXIMIZE  */
    MINIMIZE = 285,                /* MINIMIZE  */
    OF = 286,                      /* OF  */
    SATISFY = 287,                 /* SATISFY  */
    OUTPUT = 288,                  /* OUTPUT  */
    PREDICATE = 289,               /* PREDICATE  */
    RECORD = 290,                  /* RECORD  */
    SET = 291,                     /* SET  */
    SHOW = 292,                    /* SHOW  */
    SHOWCOND = 293,                /* SHOWCOND  */
    SOLVE = 294,                   /* SOLVE  */
    STRING = 295,                  /* STRING  */
    TEST = 296,                    /* TEST  */
    THEN = 297,                    /* THEN  */
    TUPLE = 298,                   /* TUPLE  */
    TYPE = 299,                    /* TYPE  */
    VARIANT_RECORD = 300,          /* VARIANT_RECORD  */
    WHERE = 301                    /* WHERE  */
  };
  typedef enum yytokentype yytoken_kind_t;
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
union YYSTYPE
{
 
    int iValue; 
    char* sValue; 
    bool bValue; 
    double dValue;
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


};
typedef union YYSTYPE YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif



int yyparse (void *parm);

#endif /* !YY_YY_USERS_JDEK0001_DROPBOX_DEVELOPMENT_CHUFFED_BUILD_CHUFFED_FLATZINC_PARSER_TAB_H_INCLUDED  */

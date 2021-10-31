#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/Optional.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <memory>
#include <string>
#include <system_error>
#include <utility>
#include <vector>
using namespace llvm;
namespace cp4pp
{
    enum MemType
    {
        LOAD,
        STORE
    };
    enum Token
    {
        TOK_EOF = -1,
        TOK_FUNCTION = -2,
        TOK_EXTERN = -3,
        TOK_IDENTIFIER = -4,
        TOK_NUMBER = -5,
        TOK_IF = -6,
        TOK_ELSE = -7,
        TOK_FOR = -8,
        TOK_CHAR = -9,
        TOK_STRING = -10,
        TOK_STRVAL = -11,
        TOK_INT = -12,
        TOK_LONG = -13
    };
    class ExprAST
    {
    public:
        MemType mType;
        virtual ~ExprAST() = default;
        virtual Value *codegen() = 0;
        virtual void print() = 0;
        ExprAST *SetLoad()
        {
            mType = LOAD;
            return this;
        }
        ExprAST *SetStore()
        {
            mType = STORE;
            return this;
        }
    };
    class NumberExprAST : public ExprAST
    {
        int Val;
        Type *type;

    public:
        NumberExprAST(int Val, Type *type) : Val(Val), type(type) {}
        Value *codegen() override;
        void print() override
        {
            fprintf(stderr, "Number: %d\n", Val);
        };
    };
    class VariableExprAST : public ExprAST
    {
        std::string Name;

    public:
        VariableExprAST(const std::string &Name) : Name(Name) {}

        Value *codegen() override;
        const std::string &getName() const { return Name; }
        void print() override
        {
            fprintf(stderr, " Variable: %s\n", Name.c_str());
        };
    };
    class ArrayExprAST : public ExprAST
    {
    public:
        Type *type;
        int num;
        std::vector<int> Vals;
        ArrayExprAST(std::vector<int> Vals, Type *type, int num) : Vals(Vals), type(type), num(num){};
        Value *codegen() override;
        void print() override
        {
            fprintf(stderr, "Array[ ");
            for (auto i : Vals)
            {
                fprintf(stderr, "%d ", i);
            }
            fprintf(stderr, "]\n");
        };
    };
    class PointerExprAST : public ExprAST
    {
    public:
        std::string Name;
        std::unique_ptr<ExprAST> Index;
        PointerExprAST(std::string Name, std::unique_ptr<ExprAST> Index) : Name(Name), Index(std::move(Index)){};
        Value *codegen() override;
        void print() override
        {
            fprintf(stderr, "Pointer[ %s  ]\n", Name.c_str());
            Index->print();
        };
    };
    class LiteralExprAST : public ExprAST
    {
        std::string Str;

    public:
        LiteralExprAST(std::string Str) : Str(Str) {}
        Value *codegen() override;
        void print() override
        {
            fprintf(stderr, "Litera: [%s]\n", Str.c_str());
        };
    };
    class AsteriskExprAST : public ExprAST
    {
        std::unique_ptr<ExprAST> Operand;
        Value *codegen() override;

    public:
        AsteriskExprAST(std::unique_ptr<ExprAST> Operand) : Operand(std::move(Operand)){};
        void print() override
        {
            fprintf(stderr, "Asterisk[");
            Operand->print();
            fprintf(stderr, "]\n");
        };
    };
    class QuoteExprAST : public ExprAST
    {
        std::unique_ptr<ExprAST> Operand;
        Value *codegen() override;

    public:
        QuoteExprAST(std::unique_ptr<ExprAST> Operand) : Operand(std::move(Operand)){};
        void print() override
        {
            fprintf(stderr, "Quote[");
            Operand->print();
            fprintf(stderr, "]\n");
        };
    };
    class BinaryExprAST : public ExprAST
    {
        char Op;
        std::unique_ptr<ExprAST> LHS, RHS;

    public:
        BinaryExprAST(char Op, std::unique_ptr<ExprAST> LHS,
                      std::unique_ptr<ExprAST> RHS)
            : Op(Op), LHS(std::move(LHS)), RHS(std::move(RHS)) {}

        Value *codegen() override;
        void print() override
        {
            fprintf(stderr, "[BIN]");
            LHS->print();
            fprintf(stderr, " %c ", Op);
            RHS->print();
            fprintf(stderr, "[/bin]\n");
        };
    };
    class BodyExprAST : public ExprAST
    {
    public:
        std::vector<std::unique_ptr<ExprAST>> Bodys;

    public:
        BodyExprAST(std::vector<std::unique_ptr<ExprAST>> Bodys) : Bodys(std::move(Bodys)) {}
        Value *codegen() override;
        void print() override
        {
            for (auto &expr : Bodys)
            {
                expr->print();
            }
        };
    };
    class ForExprAST : public ExprAST
    {
    public:
        std::unique_ptr<ExprAST> Start, End, Step;
        std::unique_ptr<BodyExprAST> Body;

    public:
        ForExprAST(std::unique_ptr<ExprAST> Start,
                   std::unique_ptr<ExprAST> End,
                   std::unique_ptr<ExprAST> Step,
                   std::unique_ptr<BodyExprAST> Body) : Start(std::move(Start)),
                                                        End(std::move(End)),
                                                        Step(std::move(Step)),
                                                        Body(std::move(Body)){};
        Value *codegen() override;
        void print() override
        {
            fprintf(stderr, "For[");
            Start->print();
            End->print();
            Step->print();
            Body->print();
            fprintf(stderr, "]\n");
        };
    };
    class IfExprAST : public ExprAST
    {
    public:
        std::unique_ptr<ExprAST> Cond;
        std::unique_ptr<BodyExprAST> Then, Else;

    public:
        IfExprAST(std::unique_ptr<ExprAST> Cond, std::unique_ptr<BodyExprAST> Then,
                  std::unique_ptr<BodyExprAST> Else)
            : Cond(std::move(Cond)), Then(std::move(Then)), Else(std::move(Else)) {}

        Value *codegen() override;
        void print() override
        {
            fprintf(stderr, "IF EXPR[\n");
            Cond->print();
            fprintf(stderr, "THEN: \n");
            Then->print();
            fprintf(stderr, "ELSE: \n");
            Else->print();
            fprintf(stderr, "]\n");
        }
    };
    class CallExprAST : public ExprAST
    {
        std::string Callee;
        std::vector<std::unique_ptr<ExprAST>> Args;

    public:
        CallExprAST(const std::string &Callee,
                    std::vector<std::unique_ptr<ExprAST>> Args)
            : Callee(Callee), Args(std::move(Args)) {}

        Value *codegen() override;
        void print() override
        {
            fprintf(stderr, "Callee: %s\n", Callee.c_str());
            for (auto &arg : Args)
                arg->print();
        };
    };
    class VarExprAST : public ExprAST
    {
        bool isPtr;
        Type *type;
        std::unique_ptr<ExprAST> Num;
        std::pair<std::string, std::unique_ptr<ExprAST>> VarNames;

    public:
        VarExprAST(Type *type, bool isPtr, std::unique_ptr<ExprAST> Num,
                   std::pair<std::string, std::unique_ptr<ExprAST>> VarNames)
            : type(type), isPtr(isPtr), Num(std::move(Num)), VarNames(std::move(VarNames)) {}
        Value *codegen() override;
        void print() override
        {
            fprintf(stderr, "VarExpr: %s\n", VarNames.first.c_str());
            VarNames.second->print();
        };
    };
    class AssignExprAST : public ExprAST
    {
    public:
        std::unique_ptr<ExprAST> LEFT;
        std::unique_ptr<ExprAST> RIGHT;

    public:
        AssignExprAST(std::unique_ptr<ExprAST> LEFT, std::unique_ptr<ExprAST> RIGHT)
            : LEFT(std::move(LEFT)), RIGHT(std::move(RIGHT)){};
        Value *codegen() override;
        void print() override
        {
            fprintf(stderr, "Assign: [");
            LEFT->print();
            RIGHT->print();
            fprintf(stderr, "]\n");
        };
    };

    class PrototypeAST
    {
        std::string Name;
        Type *type;
        std::vector<std::pair<std::string, Token>> Args;
        bool IsOperator;
        unsigned Precedence;

    public:
        PrototypeAST(const std::string &Name, std::vector<std::pair<std::string, Token>> Args,
                     Type *type, bool IsOperator = false, unsigned Prec = 0)
            : Name(Name), Args(std::move(Args)), IsOperator(IsOperator),
              Precedence(Prec), type(type) {}

        Function *codegen();
        const std::string &getName() const { return Name; }

        bool isUnaryOp() const { return IsOperator && Args.size() == 1; }
        bool isBinaryOp() const { return IsOperator && Args.size() == 2; }

        char getOperatorName() const
        {
            assert(isUnaryOp() || isBinaryOp());
            return Name[Name.size() - 1];
        }

        unsigned getBinaryPrecedence() const { return Precedence; }
        void print()
        {
            fprintf(stderr, "FnName: %s\n", Name.c_str());
            for (auto type : Args)
            {
                fprintf(stderr, "\t%6s: %3d\n", type.first.c_str(), type.second);
            }
        }
    };
    class FunctionAST
    {
    public:
        std::unique_ptr<PrototypeAST> Proto;
        std::unique_ptr<BodyExprAST> Body;

    public:
        FunctionAST(std::unique_ptr<PrototypeAST> Proto,
                    std::unique_ptr<BodyExprAST> Body)
            : Proto(std::move(Proto)), Body(std::move(Body)) {}

        Function *codegen();
        void print()
        {
            Proto->print();
            Body->print();
        };
    };
}
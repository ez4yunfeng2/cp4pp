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
#include "cp4pp.h"
#include <fcntl.h>
#include <unistd.h>
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
#define chan(c) '\\c'
#define debuging fprintf(stderr, "CurTok: [%d]\n", CurTok);
#define painc fprintf(stderr, "Painc !!!!!\n");
#define isKW isKeyWord()
#define i32 Type::getInt32Ty(*TheContext)
#define i32ptr Type::getInt32PtrTy(*TheContext)
#define i8 Type::getInt8Ty(*TheContext)
#define i8ptr Type::getInt8PtrTy(*TheContext)
#define i64 Type::getInt64Ty(*TheContext)
#define i64ptr Type::getInt64PtrTy(*TheContext)
using namespace cp4pp;
using namespace llvm;
static std::map<char, int> BinopPrecedence;
static std::unique_ptr<LLVMContext> TheContext;
static std::unique_ptr<Module> TheModule;
static std::unique_ptr<IRBuilder<>> Builder;
static std::map<std::string, std::pair<Type *, AllocaInst *>> NamedValues;
static std::map<std::string, std::unique_ptr<PrototypeAST>> FunctionProtos;
static std::string IdentifierStr;
static std::pair<Type *, int> NumVal;
static std::pair<Type *, int> CurArray;
static int CurTok;
static std::string Literal;
static int TMPNUM;
static int GetTok()
{
    static int LastChar = ' ';
    while (isspace(LastChar))
        LastChar = getchar();
    if (isalpha(LastChar))
    { // identifier: [a-zA-Z][a-zA-Z0-9]*
        IdentifierStr = LastChar;
        while (isalnum((LastChar = getchar())))
            IdentifierStr += LastChar;
        if (IdentifierStr == "function")
            return TOK_FUNCTION;
        if (IdentifierStr == "extern")
            return TOK_EXTERN;
        if (IdentifierStr == "if")
            return TOK_IF;
        if (IdentifierStr == "else")
            return TOK_ELSE;
        if (IdentifierStr == "for")
            return TOK_FOR;
        if (IdentifierStr == "char")
            return TOK_CHAR;
        if (IdentifierStr == "string")
            return TOK_STRING;
        if (IdentifierStr == "int")
            return TOK_INT;
        if (IdentifierStr == "long")
            return TOK_LONG;
        return TOK_IDENTIFIER;
    }

    if (isdigit(LastChar) || LastChar == '.')
    { // Number: [0-9.]+
        std::string NumStr;

        // NumStr += LastChar;
        // LastChar = getchar();
        // if(isdigit(LastChar) || LastChar == '.' || LastChar & ('X' | 'x') ){
        //     LastChar
        // }

        do
        {
            NumStr += LastChar;
            LastChar = getchar();
        } while (isdigit(LastChar) || LastChar == '.' || LastChar == 'X' || LastChar == 'x');

        NumVal.second = strtod(NumStr.c_str(), nullptr);
        NumVal.first = i32;
        if (LastChar == ':')
        {
            LastChar = getchar();
            if (LastChar == '1')
                NumVal.first = i8;
            else if (LastChar == '4')
                NumVal.first = i32;
            else
                NumVal.first = i64;
            LastChar = getchar();
        }
        return TOK_NUMBER;
    }
    if (LastChar == '\'')
    {
        std::string NumStr;
        NumVal.first = i8;

        LastChar = getchar();
        if (LastChar == '\\')
        {
            switch (getchar())
            {
            case 'n':
                NumVal.second = '\n';
                break;
            case 'r':
                NumVal.second = '\r';
                break;
            case 't':
                NumVal.second = '\t';
                break;
            default:
                NumVal.second = 0;
                break;
            }
        }
        else
        {
            NumVal.second = LastChar;
        }
        assert(getchar() == '\'' && "检测字符错误");
        LastChar = getchar();
        return TOK_NUMBER;
    }
    if (LastChar == '\"')
    {
        Literal = "";
        bool isUnderLine = false;
        LastChar = getchar();
        while (LastChar != '\"' || isUnderLine)
        {
            if (isUnderLine)
            {
                switch (LastChar)
                {
                case '\"':
                    Literal += '\"';
                    break;
                case 'n':
                    Literal += '\n';
                case 'r':
                    Literal += '\r';
                default:
                    break;
                }
                isUnderLine = false;
            }
            else
            {
                if (LastChar == '\\')
                {
                    isUnderLine = true;
                }
                else
                {
                    Literal += LastChar;
                }
            }
            LastChar = getchar();
        }
        TMPNUM = Literal.length();
        LastChar = getchar();
        return TOK_STRVAL;
    }
    if (LastChar == '#')
    {
        do
            LastChar = getchar();
        while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');

        if (LastChar != EOF)
            return GetTok();
    }
    if (LastChar == EOF)
        return TOK_EOF;
    int ThisChar = LastChar;
    LastChar = getchar();
    return ThisChar;
}
static int GetTokPrecedence()
{
    if (!isascii(CurTok))
        return -1;
    int TokPrec = BinopPrecedence[CurTok];
    if (TokPrec <= 0)
        return -1;
    return TokPrec;
}
static int getNextToken() { return CurTok = GetTok(); }
static std::unique_ptr<ExprAST> ParseExpression();
static bool isKeyWord()
{
    Token token = (Token)CurTok;
    return token == TOK_CHAR || token == TOK_STRING || token == TOK_INT || token == TOK_LONG;
}
std::unique_ptr<ExprAST> LogError(const char *Str)
{
    debuging
        fprintf(stderr, "Error: %s\n", Str);
    return nullptr;
}
std::unique_ptr<PrototypeAST> LogErrorP(const char *Str)
{
    LogError(Str);
    return nullptr;
}
Value *LogErrorV(const char *Str)
{
    LogError(Str);
    return nullptr;
}
std::unique_ptr<FunctionAST> LogErrorF(const char *Str)
{
    LogError(Str);
    return nullptr;
}
static std::unique_ptr<PrototypeAST> ParsePrototype()
{
    std::string FnName = IdentifierStr;
    std::string argName;
    std::vector<std::pair<std::string, Token>> ArgTypes;
    if (CurTok != TOK_IDENTIFIER)
        return LogErrorP("未识别到函数名");
    getNextToken(); // eat id
    if (CurTok != '(')
        return LogErrorP("未识别到‘(‘");
    getNextToken(); // eat '('
    while (isKW)
    {
        argName = "";
        auto tok = (Token)CurTok;
        if (getNextToken() == TOK_IDENTIFIER)
            argName = IdentifierStr;
        ArgTypes.push_back(std::make_pair(argName, tok));
        if (CurTok == TOK_IDENTIFIER)
        {
            if (getNextToken() != ',')
                break;
        }
        else if (CurTok == ')')
        {
            break;
        }
        getNextToken();
    }

    if (CurTok != ')')
        return LogErrorP("未识别到 ')'");
    getNextToken();
    getNextToken();
    return std::make_unique<PrototypeAST>(FnName, ArgTypes, i32, 0 != 0, 30);
}
static std::unique_ptr<PrototypeAST> ParseExtern()
{
    getNextToken();
    return ParsePrototype();
}

static std::unique_ptr<ExprAST> ParseIdentifierExpr()
{
    std::string varName = IdentifierStr;
    std::vector<std::unique_ptr<ExprAST>> Args;
    std::unique_ptr<ExprAST> Index;
    getNextToken();
    std::unique_ptr<ExprAST> valExpr;
    std::unique_ptr<ExprAST> LHS;
    switch (CurTok)
    {
    case '=':
        getNextToken();
        valExpr = ParseExpression();
        LHS = std::make_unique<VariableExprAST>(varName);
        return std::make_unique<AssignExprAST>(std::move(LHS), std::move(valExpr));
    case '(':
        getNextToken();
        if (CurTok != ')')
        {
            while (true)
            {
                if (auto Arg = ParseExpression())
                {
                    Args.push_back(std::move(Arg));
                }
                else
                {
                    return nullptr;
                }
                if (CurTok == ')')
                    break;
                if (CurTok != ',')
                    return LogError("未识别到 ')' 或',' ");
                getNextToken();
            }
        }
        getNextToken();
        return std::make_unique<CallExprAST>(varName, std::move(Args));
    case '[':
        getNextToken();
        Index = ParseExpression();
        if (CurTok != ']')
            return LogError("数组下标识别错误");
        LHS = std::make_unique<PointerExprAST>(varName, std::move(Index));
        if (getNextToken() != '=')
            return LHS;
        getNextToken();
        valExpr = ParseExpression();
        return std::make_unique<AssignExprAST>(std::move(LHS), std::move(valExpr));
    default:
        return std::make_unique<VariableExprAST>(varName);
    }
}

static std::unique_ptr<ExprAST> ParseArrayExpr()
{
    std::vector<int> vals;
    int num = 0;
    while (getNextToken() == TOK_NUMBER)
    {
        vals.push_back(NumVal.second);
        num++;
        if (getNextToken() == ',')
            continue;
        else if (CurTok == ']')
            break;
        else
            return LogError("意料之外的字符");
    }
    if (CurTok != ']')
        return LogError("未检测到 ']'");
    getNextToken();
    if (num > CurArray.second)
        return LogError("数字成员过大");
    return std::make_unique<ArrayExprAST>(vals, CurArray.first, CurArray.second);
}

static std::unique_ptr<ExprAST> ParseVarExpr()
{
    Token tok = (Token)CurTok;
    Type *type;
    bool isPtr = false;
    std::unique_ptr<ExprAST> Num = std::make_unique<NumberExprAST>(1, i32);
    switch (tok)
    {
    case TOK_INT:
        type = i32;
        break;
    case TOK_STRING:
        isPtr = true;
        type = i8;
        break;
    case TOK_CHAR:
        type = i8;
        break;
    case TOK_LONG:
        type = i64;
        break;
    default:
        debuging return LogError("未知参数类型1");
    }
    if (getNextToken() == '[')
    {
        CurArray.first = type;
        isPtr = true;
        getNextToken();
        Num = ParseExpression();
        if (CurTok != ']')
            return LogError("未检测到数组下标结尾");
        CurArray.second = NumVal.second;
        getNextToken();
    }

    if (CurTok == '@')
    {
        switch (tok)
        {
        case TOK_INT:
            type = i32ptr;
            break;
        case TOK_STRING:
            isPtr = true;
            type = i8ptr;
            break;
        case TOK_CHAR:
            type = i8ptr;
            break;
        case TOK_LONG:
            type = i64ptr;
        default:
            return LogError("未知参数类型2");
        }
        CurArray.first = type;
        isPtr = true;
        getNextToken();
    }

    if (CurTok != TOK_IDENTIFIER)
        return LogError("未检测到标识符");
    std::string Name = IdentifierStr;
    std::unique_ptr<ExprAST> Init = nullptr;
    getNextToken();
    if (CurTok == '=')
    {
        getNextToken();
        Init = ParseExpression();
        if (!Init)
            return nullptr;
    }
    if (tok == TOK_STRING)
        Num = std::make_unique<NumberExprAST>(TMPNUM + 1, i32);
    return std::make_unique<VarExprAST>(std::move(type), isPtr, std::move(Num), std::make_pair(Name, std::move(Init)));
}

static std::unique_ptr<ExprAST> ParseNumberExpr()
{
    auto Result = std::make_unique<NumberExprAST>(NumVal.second, NumVal.first);
    getNextToken();
    return std::move(Result);
}

static std::unique_ptr<ExprAST> ParseLiteral()
{
    auto Result = std::make_unique<LiteralExprAST>(Literal);
    getNextToken();
    return std::move(Result);
}

static std::unique_ptr<ExprAST> ParseParenExpr()
{
    getNextToken(); // eat (.
    auto V = ParseExpression();
    if (!V)
        return nullptr;

    if (CurTok != ')')
        return LogError("expected ')'");
    getNextToken(); // eat ).
    return V;
}

static std::unique_ptr<BodyExprAST> ParseBodyExpr()
{
    std::vector<std::unique_ptr<ExprAST>> bodys;
    if (CurTok != '{')
        return nullptr;
    getNextToken();
    while (auto Expr = ParseExpression())
    {
        bodys.push_back(std::move(Expr));
        if (CurTok == '}')
            break;
    }
    getNextToken();
    return std::make_unique<BodyExprAST>(std::move(bodys));
}

static std::unique_ptr<ExprAST> ParseIfExpr()
{
    getNextToken();
    auto Cond = ParseExpression();
    if (!Cond)
        return nullptr;
    if (CurTok != '{')
        return LogError("未识别到语句块");
    auto Then = ParseBodyExpr();
    if (!Then)
        return nullptr;
    if (CurTok != TOK_ELSE)
        return LogError("未识别到ELSE");
    getNextToken();
    if (CurTok != '{')
        return LogError("未识别到语句块");
    auto Else = ParseBodyExpr();
    if (!Else)
        return nullptr;
    return std::make_unique<IfExprAST>(std::move(Cond), std::move(Then), std::move(Else));
}

static std::unique_ptr<ExprAST> ParseForExpr()
{
    if (CurTok != TOK_FOR)
        return LogError("未识别到 FOR");
    getNextToken();
    auto Start = ParseExpression();
    if (CurTok != ';')
        return LogError("!未识别到 ';'");
    getNextToken();
    auto End = ParseExpression();
    if (CurTok != ';')
        return LogError("2未识别到 ';'");
    getNextToken();
    auto Step = ParseExpression();
    if (CurTok != '{')
        return LogError("未识别到 '{'");
    auto Body = ParseBodyExpr();
    return std::make_unique<ForExprAST>(std::move(Start), std::move(End), std::move(Step), std::move(Body));
}

static std::unique_ptr<ExprAST> ParseQuote()
{
    getNextToken();
    std::unique_ptr<ExprAST> expr = ParseExpression();
    if (!expr)
        return LogError("无变量名");
    return std::make_unique<QuoteExprAST>(std::move(expr));
}
static std::unique_ptr<ExprAST> ParseAsterisk()
{
    getNextToken();
    std::unique_ptr<ExprAST> expr = ParseExpression();
    if (!expr)
        return LogError("无变量名");
    return std::make_unique<AsteriskExprAST>(std::move(expr));
}
static std::unique_ptr<ExprAST> ParsePrimary()
{
    switch (CurTok)
    {
    case TOK_IF:
        return ParseIfExpr();
    case TOK_FOR:
        return ParseForExpr();
    case TOK_IDENTIFIER:
        return ParseIdentifierExpr();
    case TOK_STRING:
    case TOK_CHAR:
    case TOK_INT:
    case TOK_LONG:
        return ParseVarExpr();
    case TOK_NUMBER:
        return ParseNumberExpr();
    case TOK_STRVAL:
        return ParseLiteral();
    case '}':
        return nullptr;
    case '(':
        return ParseParenExpr();
    case '[':
        return ParseArrayExpr();
    case '&':
        return ParseQuote();
    case '@':
        return ParseAsterisk();
    default:
        fprintf(stderr, "[%d]", CurTok);
        return LogError("未知表达式");
    }
}

static std::unique_ptr<ExprAST> ParseBinOpRHS(int ExprPrec, std::unique_ptr<ExprAST> LHS)
{

    while (true)
    {
        int TokPrec = GetTokPrecedence();
        if (TokPrec < ExprPrec)
            return LHS;
        int BinOp = CurTok;
        if (BinOp == '!' || BinOp == '@')
        {
            if (getNextToken() != '=')
            {
                return LogError("未知二元操作符");
            }
        }

        getNextToken();
        auto RHS = ParsePrimary();
        if (!RHS)
            return nullptr;
        int NextPrec = GetTokPrecedence();
        if (TokPrec < NextPrec)
        {
            RHS = ParseBinOpRHS(TokPrec + 1, std::move(RHS));
            if (!RHS)
                return nullptr;
        }
        LHS = std::make_unique<BinaryExprAST>(BinOp, std::move(LHS), std::move(RHS));
    }
}

static std::unique_ptr<ExprAST> ParseExpression()
{
    auto LHS = ParsePrimary();
    return ParseBinOpRHS(0, std::move(LHS));
}

static std::unique_ptr<FunctionAST> ParseDefinition()
{
    std::unique_ptr<BodyExprAST> bodys;
    getNextToken();
    auto Proto = ParsePrototype();
    if (!Proto)
        return nullptr;
    bodys = ParseBodyExpr();
    return std::make_unique<FunctionAST>(std::move(Proto), std::move(bodys));
}

static void HandlerExtern()
{
    if (auto ProtoAST = ParseExtern())
    {
        ProtoAST->print();
        if (ProtoAST->codegen())
        {
        }
    }
    else
    {
        getNextToken();
    }
}
static void HandleFunction()
{
    if (auto FnAST = ParseDefinition())
    {
        FnAST->print();
        if (auto FnIR = FnAST->codegen())
        {
            //FnIR->print(errs());
        }
    }
    else
    {
        getNextToken();
    }
}
static void MainLoop()
{
    while (true)
    {
        switch (CurTok)
        {
        case TOK_EOF:
            return;
        case TOK_FUNCTION:
            HandleFunction();
            break;
        case TOK_EXTERN:
            HandlerExtern();
            break;
        default:
            break;
        }
    }
}
static void InitializeModuleAndPassManager()
{
    TheContext = std::make_unique<LLVMContext>();
    TheModule = std::make_unique<Module>("Good Good Jit", *TheContext);
    Builder = std::make_unique<IRBuilder<>>(*TheContext);
}

Value *NumberExprAST::codegen()
{
    return ConstantInt::get(type, Val);
}

Value *VariableExprAST::codegen()
{
    auto V = NamedValues[Name];
    if (!V.second)
    {
        fprintf(stderr, "Unknow Name: %s\n", Name.c_str());
        return LogErrorV("未知变量名");
    }

    switch (mType)
    {
    case LOAD:
        return Builder->CreateLoad(V.second, Name.c_str());
    case STORE:
        return V.second;
    default:
        break;
    }
    fprintf(stderr, "Name: %s\n", Name.c_str());
    return LogErrorV("未知存储类型");
}

Value *AssignExprAST::codegen()
{
    auto LHS = LEFT->SetStore()->codegen();
    auto RHS = RIGHT->SetLoad()->codegen();
    if (!LHS || !RHS)
        return LogErrorV("不可描述的错误");
    return Builder->CreateStore(RHS, LHS);
}
Value *ForExprAST::codegen()
{
    Value *StartVal = Start->codegen();
    if (!StartVal)
        return nullptr;
    Function *TheFunction = Builder->GetInsertBlock()->getParent();
    BasicBlock *PreheaderBB = Builder->GetInsertBlock();
    BasicBlock *LoopBB = BasicBlock::Create(*TheContext, "loop", TheFunction);
    Builder->CreateBr(LoopBB);
    Builder->SetInsertPoint(LoopBB);
    if (!Body->codegen())
        return nullptr;
    Value *StepVal = Step->codegen();
    if (!StepVal)
        return nullptr;
    Value *EndCond = End->codegen();
    if (!EndCond)
        End->codegen();
    EndCond = Builder->CreateIntCast(EndCond, i32, false);
    EndCond = Builder->CreateICmpNE(EndCond, ConstantInt::get(i32, 0), "loopcond");
    BasicBlock *LoopEndBB = Builder->GetInsertBlock();
    BasicBlock *AfterBB = BasicBlock::Create(*TheContext, "afterloop", TheFunction);
    Builder->CreateCondBr(EndCond, LoopBB, AfterBB);
    Builder->SetInsertPoint(AfterBB);
    return Constant::getNullValue(Type::getDoubleTy(*TheContext));
}

Value *IfExprAST::codegen()
{
    Value *CondV = Cond->codegen();
    assert(CondV->getType()->getTypeID() == ConstantInt::get(i32, 0)->getType()->getTypeID());

    CondV = Builder->CreateIntCast(CondV, i32, false);
    assert(CondV->getType() == ConstantInt::get(i32, 0)->getType());
    CondV = Builder->CreateICmpNE(CondV, ConstantInt::get(i32, 0), "ifcond");

    BasicBlock *MainBB = Builder->GetInsertBlock();
    Function *TheFunction = Builder->GetInsertBlock()->getParent();
    BasicBlock *ThenBB = BasicBlock::Create(*TheContext, "Then", TheFunction);
    BasicBlock *ElseBB = BasicBlock::Create(*TheContext, "Else");
    BasicBlock *MergeBB = BasicBlock::Create(*TheContext, "MergeBB");
    Builder->CreateCondBr(CondV, ThenBB, ElseBB);
    Builder->SetInsertPoint(ThenBB);
    Value *ThenV = Then->codegen();
    Builder->CreateBr(MergeBB);

    TheFunction->getBasicBlockList().push_back(ElseBB);
    Builder->SetInsertPoint(ElseBB);
    Value *ElseV = Else->codegen();
    Builder->CreateBr(MergeBB);

    TheFunction->getBasicBlockList().push_back(MergeBB);
    Builder->SetInsertPoint(MergeBB);
    PHINode *PHI = Builder->CreatePHI(i32, 2, "ifexpr");
    PHI->addIncoming(ConstantInt::get(i32, 0), ThenBB);
    PHI->addIncoming(ConstantInt::get(i32, 0), ElseBB);
    return PHI;
}

Value *BinaryExprAST::codegen()
{
    Value *L = LHS->SetLoad()->codegen();
    Value *R = RHS->SetLoad()->codegen();
    if (!L || !R)
        return nullptr;
    switch (Op)
    {
    case '+':
        return Builder->CreateAdd(L, R, "addtmp");
    case '-':
        return Builder->CreateSub(L, R, "subtmp");
    case '*':
        return Builder->CreateMul(L, R, "multmp");
    case '<':
        return Builder->CreateICmpULT(L, R, "lecmp");
    case '>':
        return Builder->CreateICmpULT(R, L, "gecmp");
    case '!':
        return Builder->CreateICmpNE(R, L, "necmp");
    case '@':
        return Builder->CreateICmpEQ(R, L, "eqcmp");
    default:
        return LogErrorV("未知操作符");
    }
}

Value *CallExprAST::codegen()
{
    Function *CalleeF = TheModule->getFunction(Callee);

    if (!CalleeF)
        return LogErrorV("未知函数引用");
    if (CalleeF->arg_size() != Args.size())
        return LogErrorV("参数不一致");
    std::vector<Value *> Argvs;
    for (unsigned i = 0, e = Args.size(); i != e; ++i)
    {
        Type *type = CalleeF->getArg(i)->getType();
        if (type->isPointerTy())
            Argvs.push_back(Args[i]->SetStore()->codegen());
        else if (type->isArrayTy())
            Argvs.push_back(Args[i]->SetStore()->codegen());
        else
            Argvs.push_back(Args[i]->SetLoad()->codegen());
        if (!Argvs.back())
            return nullptr;
    }
    return Builder->CreateCall(CalleeF, Argvs, "call_" + CalleeF->getName());
}

Value *VarExprAST::codegen()
{
    Function *TheFunction = Builder->GetInsertBlock()->getParent();
    IRBuilder<> TmpB(&TheFunction->getEntryBlock(),
                     TheFunction->getEntryBlock().begin());
    Value *arraySize = Num->codegen();
    AllocaInst *Alloca = TmpB.CreateAlloca(type, arraySize, VarNames.first);
    NamedValues[VarNames.first] = std::make_pair(type, Alloca);
    fprintf(stderr, "Name Put: %s\n", VarNames.first.c_str());
    Value *val = VarNames.second->SetLoad()->codegen();
    return Builder->CreateStore(val, Alloca);
}

Function *FunctionAST::codegen()
{
    Function *function = TheModule->getFunction(Proto->getName());
    if (!function)
        function = Proto->codegen();
    if (!function)
        return nullptr;
    BasicBlock *BB = BasicBlock::Create(*TheContext, Proto->getName(), function);
    Builder->SetInsertPoint(BB);
    NamedValues.clear();
    for (auto &arg : function->args())
    {
        IRBuilder<> TmpB(&function->getEntryBlock(),
                         function->getEntryBlock().begin());
        AllocaInst *Alloca = TmpB.CreateAlloca(arg.getType(), nullptr, arg.getName());
        Builder->CreateStore(&arg, Alloca);
        NamedValues[std::string(arg.getName())] = std::make_pair(arg.getType(), Alloca);
    }
    Value *ret = Body->codegen();
    verifyFunction(*function);
    Builder->CreateRet(ret);
    return function;
}

Value *BodyExprAST::codegen()
{
    Value *val;
    for (auto &expr : Bodys)
    {
        val = expr->codegen();
    }
    if (!val)
        val = ConstantInt::get(i32, 0);
    return val;
}
// :"Literal here"
Value *LiteralExprAST::codegen()
{
    std::vector<Constant *> vals;
    bool isUnderline = false;
    for (char ch : Str)
        vals.push_back(ConstantInt::get(i8, ch));
    vals.push_back(ConstantInt::get(i8, 0));
    return ConstantArray::get(ArrayType::get(i8, Str.length()), vals);
}
// :[1,2,3,4,5,6,7,8,9,10]
Value *ArrayExprAST::codegen()
{
    std::vector<Constant *> arrVals;
    for (auto val : Vals)
        arrVals.push_back(ConstantInt::get(type, val));
    ArrayType *arrType = ArrayType::get(type, num);
    return ConstantArray::get(arrType, arrVals);
}
// :arr[10
Value *PointerExprAST::codegen()
{
    auto V = NamedValues[Name];

    Value *index = Index->SetLoad()->codegen();
    if (!index)
        return nullptr;
    Value *ret;
    auto arrVal = Builder->CreateInBoundsGEP(V.second, index);
    switch (mType)
    {
    case LOAD:
        ret = Builder->CreateLoad(arrVal);
        break;
    case STORE:
        ret = arrVal;
        break;
    default:
        return LogErrorV("未知指针存储类型");
    }
    return ret;
}

Value *AsteriskExprAST::codegen()
{
    Value *ret;
    switch (mType)
    {
    case STORE:
        ret = Operand->SetStore()->codegen();
    case LOAD:
        ret = Operand->SetLoad()->codegen();
    default:
        ret = LogErrorV("未识别的存储类型");
        break;
    }
    return ret;
}
Value *QuoteExprAST::codegen()
{
    return Operand->SetStore()->codegen();
}

Function *PrototypeAST::codegen()
{
    std::vector<Type *> argTypes;
    std::vector<std::string> argNames;
    for (auto val : Args)
    {
        Type *type;
        argNames.push_back(val.first);
        switch (val.second)
        {
        case TOK_INT:
            type = i32;
            break;
        case TOK_STRING:
            type = i8ptr;
            break;
        case TOK_CHAR:
            type = i8;
            break;
        case TOK_LONG:
            type = i64;
        default:
            type = i32;
            break;
        }
        argTypes.push_back(type);
    }
    FunctionType *FT = FunctionType::get(type, argTypes, false);
    Function *F = Function::Create(FT, Function::ExternalLinkage, Name, TheModule.get());
    unsigned Idx = 0;
    for (auto &Arg : F->args())
    {
        Arg.setName(argNames[Idx++]);
    }
    return F;
}

int main(int argc, char **argv)
{
    close(0);
    if (argc == 2)
        open(argv[1], O_RDONLY);
    else
        open("demo.cp4pp", O_RDONLY);
    BinopPrecedence['@'] = 10;
    BinopPrecedence['!'] = 10;
    BinopPrecedence['<'] = 10;
    BinopPrecedence['>'] = 10;
    BinopPrecedence['+'] = 20;
    BinopPrecedence['-'] = 20;
    BinopPrecedence['*'] = 40;
    InitializeModuleAndPassManager();
    InitializeAllTargetInfos();
    InitializeAllTargets();
    InitializeAllTargetMCs();
    InitializeAllAsmParsers();
    InitializeAllAsmPrinters();

    getNextToken();
    MainLoop();

    auto TargetTriple = sys::getDefaultTargetTriple();
    TheModule->setTargetTriple(TargetTriple);
    std::string Error;
    auto Target = TargetRegistry::lookupTarget(TargetTriple, Error);
    if (!Target)
    {
        errs() << Error;
        return 1;
    }
    auto CPU = "generic";
    auto Features = "";
    TargetOptions opt;
    auto RM = Optional<Reloc::Model>();
    auto TheTargetMachine = Target->createTargetMachine(TargetTriple, CPU, Features, opt, RM);
    TheModule->setDataLayout(TheTargetMachine->createDataLayout());
    auto Filename = "output.o";
    std::error_code EC;
    raw_fd_ostream dest(Filename, EC, sys::fs::OF_None);
    if (EC)
    {
        errs() << "Could not open file: " << EC.message();
        return 1;
    }
    legacy::PassManager pass;
    auto FileType = CGFT_ObjectFile;
    if (TheTargetMachine->addPassesToEmitFile(pass, dest, nullptr, FileType))
    {
        errs() << "TheTargetMachine can't emit a file of this type";
        return 1;
    }
    TheModule->print(errs(), nullptr);

    auto Module = TheModule.get();
    pass.run(*Module);
    dest.flush();
    outs() << "Wrote " << Filename << "\n";
    return 0;
}
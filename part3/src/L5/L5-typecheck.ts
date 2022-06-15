// L5-typecheck
// ========================================================
import { equals, filter, flatten, includes, map, intersection, zipWith, reduce, sort } from 'ramda';
import { isAppExp, isBoolExp, isDefineExp, isIfExp, isLetrecExp, isLetExp, isNumExp,
         isPrimOp, isProcExp, isProgram, isStrExp, isVarRef, unparse, parseL51,
         AppExp, BoolExp, DefineExp, Exp, IfExp, LetrecExp, LetExp, NumExp, SetExp, LitExp,
         Parsed, PrimOp, ProcExp, Program, StrExp, isSetExp, isLitExp, 
         isDefineTypeExp, isTypeCaseExp, DefineTypeExp, TypeCaseExp, CaseExp, makeBoolExp, VarDecl, makeTypeCaseExp } from "./L5-ast";
import { applyTEnv, makeEmptyTEnv, makeExtendTEnv, TEnv } from "./TEnv";
import { isProcTExp, makeBoolTExp, makeNumTExp, makeProcTExp, makeStrTExp, makeVoidTExp,
         parseTE, unparseTExp, Record,
         BoolTExp, NumTExp, StrTExp, TExp, VoidTExp, UserDefinedTExp, isUserDefinedTExp, UDTExp, 
         isNumTExp, isBoolTExp, isStrTExp, isVoidTExp, makeSymbolTExp , isSymbolTExp ,
         isRecord, ProcTExp, makeUserDefinedNameTExp, Field, makeAnyTExp, isAnyTExp, isUserDefinedNameTExp, makePrimOpTExp, isTVar, isCompoundTExp } from "./TExp";
import { isEmpty, allT, first, rest, cons } from '../shared/list';
import { Result, makeFailure, bind, makeOk, zipWithResult, mapv, mapResult, isFailure, either, isOk } from '../shared/result';
import { isClosure ,SExpValue , isSymbolSExp , isEmptySExp } from './L5-value';
import * as Pred from '../shared/type-predicates';

const util = require('util')


// L51
export const getTypeDefinitions = (p: Program): UserDefinedTExp[] => {
    const iter = (head: Exp, tail: Exp[]): UserDefinedTExp[] =>
        isEmpty(tail) && isDefineTypeExp(head) ? [head.udType] :
        isEmpty(tail) ? [] :
        isDefineTypeExp(head) ? cons(head.udType, iter(first(tail), rest(tail))) :
        iter(first(tail), rest(tail));
    return isEmpty(p.exps) ? [] :
        iter(first(p.exps), rest(p.exps));
}

// L51
export const getDefinitions = (p: Program): DefineExp[] => {
    const iter = (head: Exp, tail: Exp[]): DefineExp[] =>
        isEmpty(tail) && isDefineExp(head) ? [head] :
        isEmpty(tail) ? [] :
        isDefineExp(head) ? cons(head, iter(first(tail), rest(tail))) :
        iter(first(tail), rest(tail));
    return isEmpty(p.exps) ? [] :
        iter(first(p.exps), rest(p.exps));
}

// L51
export const getRecords = (p: Program): Record[] =>
    flatten(map((ud: UserDefinedTExp) => ud.records, getTypeDefinitions(p)));

// L51
export const getItemByName = <T extends {typeName: string}>(typeName: string, items: T[]): Result<T> =>
    isEmpty(items) ? makeFailure(`${typeName} not found`) :
    first(items).typeName === typeName ? makeOk(first(items)) :
    getItemByName(typeName, rest(items));

// L51
export const getUserDefinedTypeByName = (typeName: string, p: Program): Result<UserDefinedTExp> =>
    getItemByName(typeName, getTypeDefinitions(p));

// L51
export const getRecordByName = (typeName: string, p: Program): Result<Record> =>
    getItemByName(typeName, getRecords(p));

// L51
// Given the name of record, return the list of UD Types that contain this record as a case.
export const getRecordParents = (typeName: string, p: Program): UserDefinedTExp[] =>
    filter((ud: UserDefinedTExp): boolean => map((rec: Record) => rec.typeName, ud.records).includes(typeName),
        getTypeDefinitions(p));


// L51
// Given a user defined type name, return the Record or UD Type which it names.
// (Note: TS fails to type check either in this case)
export const getTypeByName = (typeName: string, p: Program): Result<UDTExp> => {
    const ud = getUserDefinedTypeByName(typeName, p);
    if (isFailure(ud)) {
        return getRecordByName(typeName, p);
    } else {
        return ud;
    }
}

// TODO L51?
// Is te1 a subtype of te2?
const isSubType = (te1: TExp, te2: TExp, p: Program): boolean =>{
    if (isAnyTExp(te2))
        return true;
    else if (isUserDefinedNameTExp(te1) && isUserDefinedNameTExp(te2)  || isUserDefinedNameTExp(te1) && isUserDefinedTExp(te2)){
        const te2UDTexp: Result<UserDefinedTExp> = getUserDefinedTypeByName(te2.typeName , p);
        if(isOk(te2UDTexp))
            return isOk(te2UDTexp) ? (getRecordParents(te1.typeName , p).includes(te2UDTexp.value)) : false;
        else return false;
    }
    else return false;}


// TODO L51?: Change this definition to account for user defined types
// Purpose: Check that the computed type te1 can be accepted as an instance of te2
// test that te1 is either the same as te2 or more specific
// Deal with case of user defined type names 
// Exp is only passed for documentation purposes.
// p is passed to provide the context of all user defined types
export const checkEqualType = (te1: TExp, te2: TExp, exp: Exp, p: Program): Result<TExp> =>
  equals(te1, te2) ? makeOk(te2) :
  isSubType(te1 , te2 ,p) ? makeOk(te2):
  makeFailure(`Incompatible types: ${te1} and ${te2} in ${exp}`);


// L51
// Return te and its parents in type hierarchy to compute type cover
// Return type names (not their definition)
export const getParentsType = (te: TExp, p: Program): TExp[] =>
    (isNumTExp(te) || isBoolTExp(te) || isStrTExp(te) || isVoidTExp(te) || isAnyTExp(te)) ? [te] :
    isProcTExp(te) ? [te] :
    isUserDefinedTExp(te) ? [te] :
    isRecord(te) ? getParentsType(makeUserDefinedNameTExp(te.typeName), p) :
    isUserDefinedNameTExp(te) ?
        either(getUserDefinedTypeByName(te.typeName, p),
                (ud: UserDefinedTExp) => [makeUserDefinedNameTExp(ud.typeName)],
                (_) => either(getRecordByName(te.typeName, p),
                            (rec: Record) => cons(makeUserDefinedNameTExp(rec.typeName), 
                                                  map((ud) => makeUserDefinedNameTExp(ud.typeName), 
                                                      getRecordParents(rec.typeName, p))),
                            (_) => [])) : 
    [];

// L51
// Get the list of types that cover all ts in types.
export const coverTypes = (types: TExp[], p: Program): TExp[] =>  {
    // [[p11, p12], [p21], [p31, p32]] --> types in intersection of all lists
    const parentsList : TExp[][] = map((t) => getParentsType(t,p), types);
    return reduce<TExp[], TExp[]>(intersection, first(parentsList), rest(parentsList));
}

// Return the most specific in a list of TExps
// For example given UD(R1, R2):
// - mostSpecificType([R1, R2, UD]) = R1 (choses first out of record level)
// - mostSpecificType([R1, number]) = number  
export const mostSpecificType = (types: TExp[], p: Program): TExp =>
    reduce((min: TExp, element: TExp) => isSubType(element, min, p) ? element : min, 
            makeAnyTExp(),
            types);

// L51
// Check that all t in types can be covered by a single parent type (not by 'any')
// Return most specific parent
export const checkCoverType = (types: TExp[], p: Program): Result<TExp> => {
    const cover = coverTypes(types, p);
    return isEmpty(cover) ? makeFailure(`No type found to cover ${map((t) => JSON.stringify(unparseTExp(t), null, 2), types).join(" ")}`) :
    makeOk(mostSpecificType(cover, p));
}


// Compute the initial TEnv given user defined types
// =================================================
// TODO L51
// Construct type environment for the user-defined type induced functions
// Type constructor for all records
// Type predicate for all records
// Type predicate for all user-defined-types
// All globally defined variables (with define)

// TODO: Define here auxiliary functions for TEnv computation

// TOODO L51
// Initialize TEnv with:
// * Type of global variables (define expressions at top level of p)
// * Type of implicitly defined procedures for user defined types (define-type expressions in p)
export const initTEnv = (p: Program): TEnv =>{
    const typeDef: UserDefinedTExp[] = getTypeDefinitions(p)
    const records: Record[] = getRecords(p)
    const initialEnv:TEnv = makeEmptyTEnv();
    const  definitions: DefineExp[] = getDefinitions(p);

    const definitionsNames:string[] = map( (def:DefineExp) => def.var.var , definitions);
    const definitionsType: TExp[] = map((def:DefineExp) => def.var.texp , definitions);

    const UDPredicatesNames:string[] = map((UD: UserDefinedTExp) => `${UD.typeName}?` , typeDef);
    const UDPredicates:ProcTExp[] = map(  (UD: UserDefinedTExp) => typePredGen() , typeDef);

    const recordsPredicatesNames:string[] = map(  (rec: Record) => `${rec.typeName}?` , records);
    const recordsPredicates:ProcTExp[] = map(  (rec: Record) => typePredGen() , records);

    const recordsConstructorsNames:string[] = map(  (rec: Record) => `make-${rec.typeName}` , records);
    const recordsConstructors:ProcTExp[] = map(  (rec: Record) => recordsConstructorGen(rec , p) , records);
    
    const functionsNames:string[] = [...UDPredicatesNames , ...recordsPredicatesNames , ...recordsConstructorsNames , ...definitionsNames];
    const functions:TExp[] = [...UDPredicates , ...recordsPredicates , ...recordsConstructors , ...definitionsType];

    return makeExtendTEnv(functionsNames , functions , initialEnv);

}
const recordsConstructorGen = (rec: Record , p:Program): ProcTExp =>{
    const type:Result<UDTExp>  = getTypeByName(rec.typeName ,p);
    const fieldsType:TExp[] = map((field:Field) => field.te , rec.fields);
    if (isOk(type))
       return makeProcTExp( fieldsType  , makeUserDefinedNameTExp(type.value.typeName) )    // return makeProcTExp( fieldsType  , type.value)
    else
        return makeProcTExp( fieldsType , makeAnyTExp() );
} 
const typePredGen = (): ProcTExp => makeProcTExp( [makeAnyTExp()]  , makeBoolTExp());
   
export const getAllRecordsByName: ((rec:Record , records:Record[])=> Record[]) = (rec:Record, records:Record[]) => filter ((currRec:Record) => currRec.typeName ===  rec.typeName  , records);
export const hasSameFields: ((records:Record[], first:Record) => boolean) = (records:Record[] , first:Record) => reduce((acc , curr)=> (acc && equals(curr.fields ,first.fields)),true,records);
export const isRecursive: (UDtype:UserDefinedTExp) => boolean = (UDtype:UserDefinedTExp) => UDtype.records.some((rec:Record) => rec.fields.some((field:Field) => equals(field.te , makeUserDefinedNameTExp(UDtype.typeName)) ))   
export const hasBaseCase: (UDtype:UserDefinedTExp) => boolean = (UDtype:UserDefinedTExp) => UDtype.records.some((rec:Record) => rec.fields.every((field:Field) => !equals(field.te , makeUserDefinedNameTExp(UDtype.typeName)) ))   
export const isGoodUDType: (UDtype:UserDefinedTExp) => boolean = (UDtype:UserDefinedTExp) => !isRecursive(UDtype) || (isRecursive(UDtype) && hasBaseCase(UDtype));

// Verify that user defined types and type-case expressions are semantically correct
// =================================================================================
// TODO L51
export const checkUserDefinedTypes = (p: Program): Result<true> =>{
    // If the same type name is defined twice with different definitions
    // If a recursive type has no base case
    const UDtypes:UserDefinedTExp[] = getTypeDefinitions(p);
    const records:Record[] = getRecords(p);
        //condition 1
    const constraint1: boolean = reduce (  (acc:boolean ,curr:Record) => curr && hasSameFields( getAllRecordsByName(curr , records) , curr)  , true , records)

        //condition 2
    const constraint2: boolean = reduce ( (acc: boolean, curr: UserDefinedTExp) =>  acc && isGoodUDType(curr) , true ,UDtypes);
    
    return (constraint1 && constraint2) ?makeOk(true) : makeFailure("one of the constraints is false");
}


// TODO L51?
export const checkTypeCase = (tc: TypeCaseExp, p: Program): Result<true> => {
    // Check that all type case expressions have exactly one clause for each constituent subtype 
    // (in any order)
    const cases:CaseExp[] = tc.cases;
    // // let new_tc = tc;

    
    // // const casesTypesNames:string[] = map( (cas:CaseExp) => cas.typeName , cases);
    // // const casesTypes:Result<TExp>[] = map((name:string )=> getTypeByName(name,p) ,casesTypesNames);
    // // const casesTypesRes : TExp[] = map((te:Result<TExp>) => isOk(te)? te.value : makeVoidTExp() , casesTypes);
    


    // if(isOk(getRecordByName(tc.typeName , p))){                 //typecase on a record!
    // const casesTypesNames:string[] = map( (cas:CaseExp) => cas.typeName , cases);
    // const casesTypes:Result<TExp>[] = map((name:string )=> getTypeByName(name,p) ,casesTypesNames);
    // const casesTypesRes : TExp[] = map((te:Result<TExp>) => isOk(te)? te.value : makeVoidTExp() , casesTypes);
    // const blabla = checkCoverType(casesTypesRes,p) 
    // if (isOk(blabla) )
    //    checkTypeCase(makeTypeCaseExp(blabla.value. , tc.val , tc.cases) , p);
    // }

    const userDefine: Result<UserDefinedTExp> = getUserDefinedTypeByName(tc.typeName , p);
    const records: Result<Record[]> = mapv (userDefine , (userDefine) => userDefine.records);

    const recordsNames: Result<string[]> = mapv(records , map( (rec:Record) => rec.typeName)  )
    const casesNames: string[] = map( (Case:CaseExp) => Case.typeName ,tc.cases)
        
        //condition 1
    const constraint1: Result<boolean> = mapv (recordsNames , (records:string[]) => equals(records.sort() , casesNames.sort()))

        //condition 2
    const constraint2: Result<boolean> = mapv (constraint1 , () => { 
            const getVarsLength = (cas: CaseExp) => cas.varDecls.length;
            const getFieldsLength = (cas:CaseExp)=> {
                const numRes = mapv(getRecordByName(cas.typeName,p), (record:Record)=> record.fields.length)
                return isFailure(numRes) ? -1 : numRes.value;
            }
            return reduce(  (acc, curr) => (acc && (getVarsLength(curr) === getFieldsLength(curr))) ,  true , cases)

    }  )
    return isOk(constraint2)? makeOk(true): makeFailure(constraint2.message);

}




// Compute the type of L5 AST exps to TE
// ===============================================
// Compute a Typed-L5 AST exp to a Texp on the basis
// of its structure and the annotations it contains.

// Purpose: Compute the type of a concrete fully-typed expression
export const L51typeofProgram = (concreteExp: string): Result<string> =>
    bind(parseL51(concreteExp), (p: Program) =>
        bind(typeofExp(p, initTEnv(p), p), unparseTExp));

// For tests on a single expression - wrap the expression in a program
export const L51typeof = (concreteExp: string): Result<string> =>
    L51typeofProgram(`(L51 ${concreteExp})`);

// Purpose: Compute the type of an expression
// Traverse the AST and check the type according to the exp type.
// We assume that all variables and procedures have been explicitly typed in the program.
export const typeofExp = (exp: Parsed, tenv: TEnv, p: Program): Result<TExp> =>
    isNumExp(exp) ? makeOk(typeofNum(exp)) :
    isBoolExp(exp) ? makeOk(typeofBool(exp)) :
    isStrExp(exp) ? makeOk(typeofStr(exp)) :
    isPrimOp(exp) ? typeofPrim(exp) :
    isVarRef(exp) ? applyTEnv(tenv, exp.var) :
    isIfExp(exp) ? typeofIf(exp, tenv, p) :
    isProcExp(exp) ? typeofProc(exp, tenv, p) :
    isAppExp(exp) ? typeofApp(exp, tenv, p) :
    isLetExp(exp) ? typeofLet(exp, tenv, p) :
    isLetrecExp(exp) ? typeofLetrec(exp, tenv, p) :
    isDefineExp(exp) ? typeofDefine(exp, tenv, p) :
    isProgram(exp) ? typeofProgram(exp, tenv, p) :
    isSetExp(exp) ? typeofSet(exp, tenv, p) :
    isLitExp(exp) ? typeofLit(exp, tenv, p) :
    isDefineTypeExp(exp) ? typeofDefineType(exp, tenv, p) :
    isTypeCaseExp(exp) ? typeofTypeCase(exp, tenv, p) :
    makeFailure(`Unknown type: ${JSON.stringify(exp, null, 2)}`);

// Purpose: Compute the type of a sequence of expressions
// Check all the exps in a sequence - return type of last.
// Pre-conditions: exps is not empty.
export const typeofExps = (exps: Exp[], tenv: TEnv, p: Program): Result<TExp> =>
    isEmpty(rest(exps)) ? typeofExp(first(exps), tenv, p) :
    bind(typeofExp(first(exps), tenv, p), _ => typeofExps(rest(exps), tenv, p));

// a number literal has type num-te
export const typeofNum = (n: NumExp): NumTExp => makeNumTExp();

// a boolean literal has type bool-te
export const typeofBool = (b: BoolExp): BoolTExp => makeBoolTExp();

// a string literal has type str-te
const typeofStr = (s: StrExp): StrTExp => makeStrTExp();

// primitive ops have known proc-te types
const numOpTExp = parseTE('(number * number -> number)');
const numCompTExp = parseTE('(number * number -> boolean)');
const boolOpTExp = parseTE('(boolean * boolean -> boolean)');

// L51 Todo: cons, car, cdr, list
export const typeofPrim = (p: PrimOp): Result<TExp> =>
    (p.op === '+') ? numOpTExp :
    (p.op === '-') ? numOpTExp :
    (p.op === '*') ? numOpTExp :
    (p.op === '/') ? numOpTExp :
    (p.op === 'and') ? boolOpTExp :
    (p.op === 'or') ? boolOpTExp :
    (p.op === '>') ? numCompTExp :
    (p.op === '<') ? numCompTExp :
    (p.op === '=') ? numCompTExp :
    // Important to use a different signature for each op with a TVar to avoid capture
    (p.op === 'number?') ? parseTE('(T -> boolean)') :
    (p.op === 'boolean?') ? parseTE('(T -> boolean)') :
    (p.op === 'string?') ? parseTE('(T -> boolean)') :
    (p.op === 'list?') ? parseTE('(T -> boolean)') :
    (p.op === 'pair?') ? parseTE('(T -> boolean)') :
    (p.op === 'symbol?') ? parseTE('(T -> boolean)') :
    (p.op === 'not') ? parseTE('(boolean -> boolean)') :
    (p.op === 'eq?') ? parseTE('(T1 * T2 -> boolean)') :
    (p.op === 'string=?') ? parseTE('(T1 * T2 -> boolean)') :
    (p.op === 'display') ? parseTE('(T -> void)') :
    (p.op === 'newline') ? parseTE('(Empty -> void)') :
    makeFailure(`Primitive not yet implemented: ${p.op}`);

// TODO L51?
// Change this definition to account for possibility of subtype expressions between thenTE and altTE
// 
// Purpose: compute the type of an if-exp
// Typing rule:
//   if type<test>(tenv) = boolean
//      type<then>(tenv) = t1
//      type<else>(tenv) = t1
// then type<(if test then else)>(tenv) = t1
export const typeofIf = (ifExp: IfExp, tenv: TEnv, p: Program): Result<TExp> => {
    const testTE = typeofExp(ifExp.test, tenv, p);
    const thenTE = typeofExp(ifExp.then, tenv, p);
    const altTE = typeofExp(ifExp.alt, tenv, p);
    const constraint1 = bind(testTE, testTE => checkEqualType(testTE, makeBoolTExp(), ifExp, p));   //check if test is boolean predicate
    const constraint2 = bind(thenTE, (thenTE: TExp) =>                                              //check if then is subtype of alt
                            bind(altTE, (altTE: TExp) =>
                                checkEqualType(thenTE, altTE, ifExp, p)));       
    const constraint3 = bind(altTE, (altTE: TExp) =>                                                ////check if alt is subtype of then
                            bind(thenTE, (thenTE: TExp) =>
                                checkEqualType(altTE, thenTE, ifExp, p)));    
                                                                                
    if(isOk(constraint2))
        return bind(constraint1, (_c1) => constraint2);
    else
        return bind(constraint1, (_c1) => constraint3);
};

// Purpose: compute the type of a proc-exp
// Typing rule:
// If   type<body>(extend-tenv(x1=t1,...,xn=tn; tenv)) = t
// then type<lambda (x1:t1,...,xn:tn) : t exp)>(tenv) = (t1 * ... * tn -> t)
export const typeofProc = (proc: ProcExp, tenv: TEnv, p: Program): Result<TExp> => {
    const argsTEs = map((vd) => vd.texp, proc.args);
    const extTEnv = makeExtendTEnv(map((vd) => vd.var, proc.args), argsTEs, tenv);
    const constraint1 = bind(typeofExps(proc.body, extTEnv, p), (body: TExp) => 
                            checkEqualType(body, proc.returnTE, proc, p));
    return bind(constraint1, (returnTE: TExp) => makeOk(makeProcTExp(argsTEs, returnTE)));
};

// Purpose: compute the type of an app-exp
// Typing rule:
// If   type<rator>(tenv) = (t1*..*tn -> t)
//      type<rand1>(tenv) = t1
//      ...
//      type<randn>(tenv) = tn
// then type<(rator rand1...randn)>(tenv) = t
// We also check the correct number of arguments is passed.
export const typeofApp = (app: AppExp, tenv: TEnv, p: Program): Result<TExp> =>
    bind(typeofExp(app.rator, tenv, p), (ratorTE: TExp) => {
        if (! isProcTExp(ratorTE)) {
            return bind(unparseTExp(ratorTE), (rator: string) =>
                        bind(unparse(app), (exp: string) =>
                            makeFailure<TExp>(`Application of non-procedure: ${rator} in ${exp}`)));
        }
        if (app.rands.length !== ratorTE.paramTEs.length) {
            return bind(unparse(app), (exp: string) => makeFailure<TExp>(`Wrong parameter numbers passed to proc: ${exp}`));
        }
        const constraints = zipWithResult((rand, trand) => bind(typeofExp(rand, tenv, p), (typeOfRand: TExp) => 
                                                                checkEqualType(typeOfRand, trand, app, p)),
                                          app.rands, ratorTE.paramTEs);
        return mapv(constraints, _ => ratorTE.returnTE);
    });

// Purpose: compute the type of a let-exp
// Typing rule:
// If   type<val1>(tenv) = t1
//      ...
//      type<valn>(tenv) = tn
//      type<body>(extend-tenv(var1=t1,..,varn=tn; tenv)) = t
// then type<let ((var1 val1) .. (varn valn)) body>(tenv) = t
export const typeofLet = (exp: LetExp, tenv: TEnv, p: Program): Result<TExp> => {
    const vars = map((b) => b.var.var, exp.bindings);
    const vals = map((b) => b.val, exp.bindings);
    const varTEs = map((b) => b.var.texp, exp.bindings);
    const constraints = zipWithResult((varTE, val) => bind(typeofExp(val, tenv, p), (typeOfVal: TExp) => 
                                                            checkEqualType(typeOfVal ,varTE, exp, p)),
                                      varTEs, vals);
    return bind(constraints, _ => typeofExps(exp.body, makeExtendTEnv(vars, varTEs, tenv), p));
};

// Purpose: compute the type of a letrec-exp
// We make the same assumption as in L4 that letrec only binds proc values.
// Typing rule:
//   (letrec((p1 (lambda (x11 ... x1n1) body1)) ...) body)
//   tenv-body = extend-tenv(p1=(t11*..*t1n1->t1)....; tenv)
//   tenvi = extend-tenv(xi1=ti1,..,xini=tini; tenv-body)
// If   type<body1>(tenv1) = t1
//      ...
//      type<bodyn>(tenvn) = tn
//      type<body>(tenv-body) = t
// then type<(letrec((p1 (lambda (x11 ... x1n1) body1)) ...) body)>(tenv-body) = t
export const typeofLetrec = (exp: LetrecExp, tenv: TEnv, p: Program): Result<TExp> => {
    const ps = map((b) => b.var.var, exp.bindings);
    const procs = map((b) => b.val, exp.bindings);
    if (! allT(isProcExp, procs))
        return makeFailure(`letrec - only support binding of procedures - ${JSON.stringify(exp, null, 2)}`);
    const paramss = map((p) => p.args, procs);
    const bodies = map((p) => p.body, procs);
    const tijs = map((params) => map((p) => p.texp, params), paramss);
    const tis = map((proc) => proc.returnTE, procs);
    const tenvBody = makeExtendTEnv(ps, zipWith((tij, ti) => makeProcTExp(tij, ti), tijs, tis), tenv);
    const tenvIs = zipWith((params, tij) => makeExtendTEnv(map((p) => p.var, params), tij, tenvBody),
                           paramss, tijs);
    const types = zipWithResult((bodyI, tenvI) => typeofExps(bodyI, tenvI, p), bodies, tenvIs)
    const constraints = bind(types, (types: TExp[]) => 
                            zipWithResult((typeI, ti) => checkEqualType(typeI, ti, exp, p), types, tis));
    return bind(constraints, _ => typeofExps(exp.body, tenvBody, p));
};

// TODO - write the true definition    ??????????????????????????????????????????????? 
// Purpose: compute the type of a define
// Typing rule:
//   (define (var : texp) val)
//   tenv-val = extend-tenv(var:texp; tenv)
// If   type<val>(tenv-val) = texp
// then type<(define (var : texp) val)>(tenv) = void
export const typeofDefine = (exp: DefineExp, tenv: TEnv, p: Program): Result<VoidTExp> => {
    // const v = exp.var.var;
    // const texp = exp.var.texp;
    const val = exp.val;
    // const tenvVal = makeExtendTEnv([v], [texp], tenv);
    const constraint = typeofExp(val, tenv, p);    
    return mapv(constraint, (_) => makeVoidTExp());
};

// Purpose: compute the type of a program
// Typing rule:
export const typeofProgram = (exp: Program, tenv: TEnv, p: Program): Result<TExp> =>
    typeofExps(exp.exps, tenv, p);

// TODO L51         ??????????????????????????????????????????????
// Write the typing rule for DefineType expressions
export const typeofDefineType = (exp: DefineTypeExp, _tenv: TEnv, _p: Program): Result<TExp> =>{
    // const v = exp.var.var;
    // const texp = exp.var.texp;
    // const val = exp.val;
    // const tenvVal = makeExtendTEnv([v], [texp], tenv);
    // const constraint = typeofExp(val, tenvVal, p);    
    // return mapv(constraint, (_) => makeVoidTExp());

    const udType:UserDefinedTExp = exp.udType;
    const records: Record[] = udType.records;
    const recordsNames: string[] = map ((rec:Record) => rec.typeName , records);
    const newEnv = makeExtendTEnv(recordsNames , records , _tenv);

    // const constraint1 = 
    return makeOk(makeVoidTExp());

}

// TODO L51?
export const typeofSet = (exp: SetExp, _tenv: TEnv, _p: Program): Result<TExp> =>{
    const v = exp.var.var;
    const texpRes = applyTEnv(_tenv , v);
    const val = exp.val;
    const tenvVal = mapv(texpRes,(texpRes) => makeExtendTEnv([v], [texpRes], _tenv));
    const constraint = bind (tenvVal , (tenvVal) => typeofExp(val, tenvVal, _p)) ;    
    return mapv(constraint, (_) => makeVoidTExp());
}


// TODO L51?    
// ADD support to TExp.ts: AtomicTExp disjoint union? L51?

export const typeofLit = (exp: LitExp, _tenv: TEnv, _p: Program): Result<TExp> =>{
    const val:SExpValue = exp.val;
    return Pred.isNumber(val) ?  makeOk(makeNumTExp()) :
    Pred.isBoolean(val) ? makeOk(makeBoolTExp()) :
    Pred.isString(val) ? makeOk(makeStrTExp()) :
    // isClosure(val) ? makeOk(/**makeClosureTexp() */) :
    isPrimOp(val) ? makeOk(makePrimOpTExp()) :
    isSymbolSExp(val) ? makeOk(makeSymbolTExp()) :
    // isEmptySExp(val) ? makeOk("NONE") :
    // isCompoundSExp(val) ? makeOk(/**makeCompundTexp() */) :
    makeOk(makeVoidTExp());
}
    

// TODO: L51
// Purpose: compute the type of a type-case
// Typing rule:
// For all user-defined-type id
//         with component records record_1 ... record_n
//         with fields (field_ij) (i in [1...n], j in [1..R_i])
//         val CExp
//         body_i for i in [1..n] sequences of CExp
//   ( type-case id val (record_1 (field_11 ... field_1r1) body_1)...  )
//  TODO



    export const typeofTypeCase = (exp: TypeCaseExp, tenv: TEnv, p: Program): Result<TExp> => {

    
        const constraint1:Result<true> = checkTypeCase(exp ,p );
    
        const typeOfCorrectTypeCase: (exp: TypeCaseExp) => Result<TExp> = (exp: TypeCaseExp) => {
            const cases:CaseExp[] = exp.cases;
            const newEnv = makeExtendTEnv(getCaseVarNames(cases[0]),getCaseVarTypes(cases[0] , p),tenv)
            const typeOfFirstCase = typeofExps(cases[0].body, newEnv ,p);
            const constraint2 = cases.every( (cas:CaseExp) => {
                const typeCurr = typeofExps(cas.body,makeExtendTEnv(getCaseVarNames(cas),getCaseVarTypes(cas , p),tenv),p)
                return equals (typeofExps(cas.body,makeExtendTEnv(getCaseVarNames(cas),getCaseVarTypes(cas , p),tenv),p) , typeOfFirstCase )
            } )
            return constraint2 ? typeOfFirstCase : makeFailure("case types are not equal"); 
        }
    
        return bind (constraint1 , (constraint1Res:boolean) => typeOfCorrectTypeCase(exp))
    }



// export const typeofTypeCase = (exp: TypeCaseExp, tenv: TEnv, p: Program): Result<TExp> => {

    
//     const constraint1:Result<true> = checkTypeCase(exp ,p );

//     const typeOfCorrectTypeCase: (exp: TypeCaseExp) => Result<TExp> = (exp: TypeCaseExp) => {
//         const cases:CaseExp[] = exp.cases;
//         const newEnv = makeExtendTEnv(getCaseVarNames(cases[0]),getCaseVarTypes(cases[0] , p),tenv)
//         const typeOfFirstCase = typeofExps(cases[0].body, newEnv ,p);
//         const constraint2 = cases.every( (cas:CaseExp) => {
//             const typeCurr = typeofExps(cas.body,makeExtendTEnv(getCaseVarNames(cas),getCaseVarTypes(cas , p),tenv),p)
//             return equals (typeofExps(cas.body,makeExtendTEnv(getCaseVarNames(cas),getCaseVarTypes(cas , p),tenv),p) , typeOfFirstCase )
//         } )
//         return constraint2 ? typeOfFirstCase : makeFailure("case types are not equal"); 
//     }

//     return bind (constraint1 , (constraint1Res:boolean) => typeOfCorrectTypeCase(exp))
// }

const getCaseVarNames:(cas:CaseExp) => string[] = (cas:CaseExp) => map((vd: VarDecl) => vd.var ,  cas.varDecls); 

const getCaseVarTypes:(cas:CaseExp , p:Program) => TExp[] = (cas:CaseExp ,  p:Program) =>   {
    const rec:Result<Record> = getRecordByName(cas.typeName , p);
    return isOk(rec) ? map ((fi:Field) => fi.te , rec.value.fields) : [];
}

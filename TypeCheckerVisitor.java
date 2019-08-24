import syntaxtree.*;
import java.util.*;
import visitor.GJDepthFirst;

public class TypeCheckerVisitor extends GJDepthFirst <String, STMap.Level> {

    /* the top of the symbol table that holds every class */
    STMap.SymTable GlobalSymbolTable;
    /**
    I need to know when an identifier is a
    -type (int-boolean-class name)
    or a
    -name (variable-function name)
    */
    String IdentifierType = null;
    /**
    im using call_args to put together the arguments at function call
    since, ( ExpressionTerm() )* is getting zero or many calls
    and I can't have just a return type
    */
    List<String> call_args = new ArrayList<String>();
    /**
    Initializing global symbol table where,
    * variables
    * classes
    * methods
    are stored by the first visitor.
    */
    TypeCheckerVisitor(STMap.SymTable classes){
        GlobalSymbolTable = classes;
    }

    /* we will see if classname inherits from supername */
    boolean inheritance_chain(String classname, String supername){
        if (classname == null || supername == null) return false;
        STMap.ClassST current_cl = GlobalSymbolTable.get_class(classname);
        while(current_cl.superclass != null){
            if (current_cl.superclass.equals(supername)) return true;
            current_cl = GlobalSymbolTable.get_class(current_cl.superclass);
        }
        return false;
    }

    /* checking arguments for a method call */
    boolean check_arguments(STMap.MethodST mthd){
        String arg1;
        String arg2;
        /* this.call_args have the args of the method call from ExpressionList() */
        if (this.call_args.size() == mthd.num_args()){
            for (int i = 0; i < this.call_args.size(); i++){
                arg1 = this.call_args.get(i);
                arg2 = mthd.get_arg_type(i);
                if (!arg1.equals(arg2)){
                    if (arg2.equals("int") || arg2.equals("boolean") || arg2.equals("int[]")){
                        this.call_args.clear();
                        return false;
                    }
                    /* check if arg1 is an object of derived class from arg2 */
                    String classname = GlobalSymbolTable.get_class(arg1).get_name();
                    String supername = GlobalSymbolTable.get_class(arg2).get_name();
                    if (!inheritance_chain(classname, supername)){
                        this.call_args.clear();
                        return false;
                    }
                }
            }
        }else{
            this.call_args.clear();
            return false;
        }
        this.call_args.clear();
        return true;
    }

    /* checking arguments for a method declaration */
    boolean check_arguments(STMap.MethodST mthd, STMap.MethodST mthd2){
        String arg1;
        String arg2;
        if (mthd.num_args() == mthd2.num_args()){
            for (int i = 0; i < mthd.num_args(); i++){
                arg1 = mthd.get_arg_type(i);
                arg2 = mthd2.get_arg_type(i);
                if (!arg1.equals(arg2)){
                    if (arg2.equals("int") || arg2.equals("boolean") || arg2.equals("int[]")){
                        return false;
                    }
                }
            }
        }else{
            return false;
        }
        return true;
    }

    /**
    * Grammar production:
    * f0 -> MainClass()
    * f1 -> ( TypeDeclaration() )*
    * f2 -> <EOF>
    */
    public String visit(Goal n, STMap.Level Symbol_Table) throws Exception {
        n.f0.accept(this, Symbol_Table);
        if(n.f1.present()) n.f1.accept(this, Symbol_Table);
        return null;
    }

    /**
    * Grammar production:
    * f0 -> "class"
    * f1 -> Identifier()
    * f2 -> "{"
    * f3 -> "public"
    * f4 -> "static"
    * f5 -> "void"
    * f6 -> "main"
    * f7 -> "("
    * f8 -> "String"
    * f9 -> "["
    * f10 -> "]"
    * f11 -> Identifier()
    * f12 -> ")"
    * f13 -> "{"
    * f14 -> ( VarDeclaration() )*
    * f15 -> ( Statement() )*
    * f16 -> "}"
    * f17 -> "}"
    */
    public String visit(MainClass n, STMap.Level Symbol_Table) throws Exception {
        STMap.ClassST cl = Symbol_Table.get_class(n.f1.f0.toString());
        STMap.MethodST mthd = cl.get_method("main");
        if (n.f14.present()) n.f14.accept(this, mthd);
        if (n.f15.present()) n.f15.accept(this, mthd);
        return null;
    }

    /**
    * Grammar production:
    * f0 -> "class"
    * f1 -> Identifier()
    * f2 -> "{"
    * f3 -> ( VarDeclaration() )*
    * f4 -> ( MethodDeclaration() )*
    * f5 -> "}"
    */
    public String visit(ClassDeclaration n, STMap.Level Symbol_Table) throws Exception {
        STMap.ClassST cl = Symbol_Table.get_class(n.f1.f0.toString());
        if (n.f3.present()) n.f3.accept(this, cl);
        if (n.f4.present()) n.f4.accept(this, cl);
        return null;
    }

    /**
    * Grammar production:
    * f0 -> "class"
    * f1 -> Identifier()
    * f2 -> "extends"
    * f3 -> Identifier()
    * f4 -> "{"
    * f5 -> ( VarDeclaration() )*
    * f6 -> ( MethodDeclaration() )*
    * f7 -> "}"
    */
    public String visit(ClassExtendsDeclaration n, STMap.Level Symbol_Table) throws Exception {
        STMap.ClassST cl = Symbol_Table.get_class(n.f1.f0.toString());
        if (n.f5.present()) n.f5.accept(this, cl);
        if (n.f6.present()) n.f6.accept(this, cl);
        return null;
    }

    /**
    * Grammar production:
    * f0 -> "public"
    * f1 -> Type()
    * f2 -> Identifier()
    * f3 -> "("
    * f4 -> ( FormalParameterList() )?
    * f5 -> ")"
    * f6 -> "{"
    * f7 -> ( VarDeclaration() )*
    * f8 -> ( Statement() )*
    * f9 -> "return"
    * f10 -> Expression()
    * f11 -> ";"
    * f12 -> "}"
    */
    public String visit(MethodDeclaration n, STMap.Level Symbol_Table) throws Exception {
        String type = n.f1.accept(this, Symbol_Table);
        STMap.MethodST mthd = Symbol_Table.get_method(n.f2.accept(this, Symbol_Table));
        if (n.f7.present()) n.f7.accept(this, mthd);
        if (n.f8.present()) n.f8.accept(this, mthd);
        String return_type = n.f10.accept(this, mthd);
        if (!type.equals(return_type)) throw new Exception("Error: Method return type must be " + type + " instead of " + return_type);
        if (mthd.overiding){
            /* argument check */
            STMap.ClassST spcl = GlobalSymbolTable.get_class(Symbol_Table.get_superclass());
            STMap.MethodST spmthd = spcl.get_method(mthd.name);
            if (!check_arguments(mthd, spmthd)) throw new Exception("Error: Arguments of virtual method " + mthd.name + " don't match at class " + Symbol_Table.get_name());
            /* return types check */
            String super_return_type = spmthd.type;
            if (!return_type.equals(super_return_type)) throw new Exception("Error: Return types of virtual method " + mthd.name + " don't match");
        }
        return null;
    }

    /**
    * Grammar production:
    * f0 -> Type()
    * f1 -> Identifier()
    * f2 -> ";"
    */
    public String visit(VarDeclaration n, STMap.Level Symbol_Table) throws Exception {
        STMap.VariableDL var = null;
        var = Symbol_Table.get_variable(n.f1.accept(this, var));
        if (var == null) throw new Exception("Error: Variable " + n.f1.f0.toString() + " can't be found in " + Symbol_Table.get_name());
        String vartype = var.type;
        if (!vartype.equals("int") && !vartype.equals("boolean") && !vartype.equals("int[]")){
            if (!GlobalSymbolTable.exists_class(vartype)) throw new Exception("Error: Unknown type: " + vartype);
        }
        return null;
    }

    /**
    * Grammar production:
    * f0 -> <IDENTIFIER>
    */
    public String visit(Identifier n, STMap.Level Symbol_Table) throws Exception {
        String var = n.f0.toString();
        this.IdentifierType = "name";
        return var;
    }

    /**
    * Grammar production:
    * f0 -> ArrayType()
    *       | BooleanType()
    *       | IntegerType()
    *       | Identifier()
    */
    public String visit(Type n, STMap.Level Symbol_Table) throws Exception {
        String type =  n.f0.accept(this, Symbol_Table);
        this.IdentifierType = "type";
        return type;
    }

    /**
    * Grammar production:
    * f0 -> "int"
    */
    public String visit(IntegerType n, STMap.Level Symbol_Table) throws Exception{
        String var = n.f0.toString();
        this.IdentifierType = "type";
        return var;
    }

    /**
    * Grammar production:
    * f0 -> "boolean"
    */
    public String visit(BooleanType n, STMap.Level Symbol_Table) throws Exception{
        String var = n.f0.toString();
        this.IdentifierType = "type";
        return var;
    }

    /**
    * Grammar production:
    * f0 -> "int"
    * f1 -> "["
    * f2 -> "]"
    */
    public String visit(ArrayType n, STMap.Level Symbol_Table) throws Exception {
        this.IdentifierType = "type";
        return "int[]";
    }

    /**
    * Grammar production:
    * f0 -> "{"
    * f1 -> ( Statement() )*
    * f2 -> "}"
    */
    public String visit(Block n, STMap.Level Symbol_Table) throws Exception {
        if (n.f1.present()) n.f1.accept(this, Symbol_Table);
        return null;
    }

    /**
    * Grammar production:
    * f0 -> Identifier()
    * f1 -> "="
    * f2 -> Expression()
    * f3 -> ";"
    */
    public String visit(AssignmentStatement n, STMap.Level Symbol_Table) throws Exception {
        String vname = n.f0.accept(this, Symbol_Table);
        STMap.VariableDL var = Symbol_Table.get_variable(vname);
        if (var == null){
            var = GlobalSymbolTable.get_class(Symbol_Table.get_parentclass()).get_variable(vname);
            if (var == null) throw new Exception("Assignemnt Error: There is no variable named " + vname);
        }
        String vtype = var.type;
        String expr = n.f2.accept(this, Symbol_Table);
        /* check for superclass */
        if (!vtype.equals(expr)){
            STMap.ClassST cl = GlobalSymbolTable.get_class(expr);
            if (cl == null) throw new Exception("Error: Cannot assign type " + expr + " at variable of type " + vtype);
            if (!inheritance_chain(cl.name, vtype)) throw new Exception("Error: Cannot assign type " + expr + " at variable of type " + vtype);
        }
        return null;
    }

    /**
    * Grammar production:
    * f0 -> Identifier()
    * f1 -> "["
    * f2 -> Expression()
    * f3 -> "]"
    * f4 -> "="
    * f5 -> Expression()
    * f6 -> ";"
    */
    public String visit(ArrayAssignmentStatement n, STMap.Level Symbol_Table) throws Exception {
        /* check if f0 exists as array */
        String varname = n.f0.accept(this, Symbol_Table);
        STMap.VariableDL var = Symbol_Table.get_variable(varname);
        if (var == null){
            var = GlobalSymbolTable.get_class(Symbol_Table.get_parentclass()).get_variable(varname);
            if (var == null) throw new Exception("Error: Unknown variable " + varname);
        }
        if (!var.type.equals("int[]")) throw new Exception("Error: Variable " + varname + "must be of type int[] to perform this assignment");
        /* check if f2 is IntegerType */
        String expr = n.f2.accept(this, Symbol_Table);
        if (this.IdentifierType.equals("type")){
            if (!expr.equals("int")) throw new Exception("Error: Array Index must be of type int, instead got type " + expr);
        }else{
            /* search for the type of this variable */
            STMap.VariableDL tempvar = Symbol_Table.get_variable(expr);
            if (!tempvar.type.equals("int")) throw new Exception("Error: Array Index must be of type int, instead got type " + tempvar.type);
        }
        /* check if f5 is of type int */
        expr = n.f5.accept(this, Symbol_Table);
        if (!expr.equals("int")) throw new Exception("Error: Expected type int but instead got type " + expr);
        return null;
    }

    /**
    * Grammar production:
   	* f0 -> "if"
   	* f1 -> "("
   	* f2 -> Expression
   	* f3 -> ")"
   	* f4 -> Statement
   	* f5 -> "else"
   	* f6 -> Statement
   	*/
    public String visit(IfStatement n, STMap.Level Symbol_Table) throws Exception {
        /* check if expression is of type Boolean */
        String expr = n.f2.accept(this, Symbol_Table);
        if (!expr.equals("boolean")) throw new Exception("Error: If expected expression of type boolean and got of type " + expr);
        n.f4.accept(this, Symbol_Table);
        n.f6.accept(this, Symbol_Table);
        return null;
    }

    /**
    * Grammar production:
   	* f0 -> "while"
   	* f1 -> "("
   	* f2 -> Expression
   	* f3 -> ")"
   	* f4 -> Statement
   	*/
    public String visit(WhileStatement n, STMap.Level Symbol_Table) throws Exception {
        /* check if expression is of type Boolean */
        String expr = n.f2.accept(this, Symbol_Table);
        if (!expr.equals("boolean")) throw new Exception("Error: While expected expression of type boolean and got of type " + expr);
        n.f4.accept(this, Symbol_Table);
        return null;
    }

    /**
    * Grammar production:
   	* f0 -> "System.out.println"
   	* f1 -> "("
   	* f2 -> Expression
   	* f3 -> ")"
   	* f4 -> ";"
   	*/
    public String visit(PrintStatement n, STMap.Level Symbol_Table) throws Exception {
        String expr = n.f2.accept(this, Symbol_Table);
        if (!expr.equals("int") && !expr.equals("boolean")) throw new Exception("Error: can't print type " + expr);
        return null;
    }

    /**
    * Grammar production:
    * f0 -> AndExpression()
    *       | CompareExpression()
    *       | PlusExpression()
    *       | MinusExpression()
    *       | TimesExpression()
    *       | ArrayLookup()
    *       | ArrayLength()
    *       | MessageSend()
    *       | Clause()
    */
    public String visit(Expression n, STMap.Level Symbol_Table) throws Exception {
        String expr = n.f0.accept(this, Symbol_Table);
        if (this.IdentifierType.equals("type")){
            if (expr.equals("int") || expr.equals("boolean") || expr.equals("int[]"))   return expr;
            /* search for class to create an object of this type */
            if (!GlobalSymbolTable.exists_class(expr)) throw new Exception("Error: Unknown type " + expr);
            return expr;
        }

        if (expr.equals("this")){
            STMap.ClassST cl = GlobalSymbolTable.get_class(Symbol_Table.get_parentclass());
            return cl.name;
        }else{
            /* search for the type of the identifier expr */
            if (Symbol_Table.exists_var(expr)) {
                this.IdentifierType = "type";
                return Symbol_Table.get_variable(expr).type;
            }else{
                /* search on parent class */
                String parentclassname = Symbol_Table.get_parentclass();
                STMap.ClassST parentclass = GlobalSymbolTable.get_class(parentclassname);
                if (parentclass.exists_var(expr)) {
                    this.IdentifierType = "type";
                    return parentclass.get_variable(expr).type;
                }else{
                    throw new Exception("Error: Unknown variable " + expr);
                }
            }
        }
    }

    /**
    * Grammar production:
    * f0 -> Block()
    *       | AssignmentStatement()
    *       | ArrayAssignmentStatement()
    *       | IfStatement()
    *       | WhileStatement()
    *       | PrintStatement()
    */
    public String visit(Statement n, STMap.Level Symbol_Table) throws Exception {
        return n.f0.accept(this, Symbol_Table);
    }

    /**
    * Grammar production:
    * f0 -> Clause()
    * f1 -> "&&"
    * f2 -> Clause()
    */
    public String visit(AndExpression n, STMap.Level Symbol_Table) throws Exception {
        n.f0.accept(this, Symbol_Table);
        n.f2.accept(this, Symbol_Table);
        this.IdentifierType = "type";
        return "boolean";
    }

    /**
    * Grammar production:
    * f0 -> PrimaryExpression()
    * f1 -> "<"
    * f2 -> PrimaryExpression()
    */
    public String visit(CompareExpression n, STMap.Level Symbol_Table) throws Exception {
        n.f0.accept(this, Symbol_Table);
        n.f2.accept(this, Symbol_Table);
        this.IdentifierType = "type";
        return "boolean";
    }

    /**
    * Grammar production:
    * f0 -> PrimaryExpression()
    * f1 -> "+"
    * f2 -> PrimaryExpression()
    */
    public String visit(PlusExpression n, STMap.Level Symbol_Table) throws Exception {
        n.f0.accept(this, Symbol_Table);
        n.f2.accept(this, Symbol_Table);
        this.IdentifierType = "type";
        return "int";
    }

    /**
    * Grammar production:
    * f0 -> PrimaryExpression()
    * f1 -> "-"
    * f2 -> PrimaryExpression()
    */
    public String visit(MinusExpression n, STMap.Level Symbol_Table) throws Exception {
        n.f0.accept(this, Symbol_Table);
        n.f2.accept(this, Symbol_Table);
        this.IdentifierType = "type";
        return "int";
    }

    /**
    * Grammar production:
    * f0 -> PrimaryExpression()
    * f1 -> "*"
    * f2 -> PrimaryExpression()
    */
    public String visit(TimesExpression n, STMap.Level Symbol_Table) throws Exception {
        n.f0.accept(this, Symbol_Table);
        n.f2.accept(this, Symbol_Table);
        this.IdentifierType = "type";
        return "int";
    }

    /**
    * Grammar production:
    * f0 -> "!"
    * f1 -> Clause()
    */
    public String visit(NotExpression n, STMap.Level Symbol_Table) throws Exception {
        n.f1.accept(this, Symbol_Table);
        this.IdentifierType = "type";
        return "boolean";
    }

    /**
    * Grammar production:
    * f0 -> PrimaryExpression
    * f1 -> "."
    * f2 -> Identifier
    * f3 -> "("
    * f4 -> ( ExpressionList )?
    * f5 -> ")"
    */
    public String visit(MessageSend n, STMap.Level Symbol_Table) throws Exception {
        String expr = n.f0.accept(this, Symbol_Table);
        STMap.ClassST cl = null;
        /* in case of class name or primitive type */
        if (this.IdentifierType.equals("type")) {
            if (expr.equals("int") || expr.equals("boolean") || expr.equals("int[]")) throw new Exception("Can't call a method for type " + expr);
            cl = GlobalSymbolTable.get_class(expr);
        }else{
            /* in case we have a variable name -> we have to find the type */
            if (expr.equals("this")){
                String parentclass = Symbol_Table.get_parentclass();
                cl = GlobalSymbolTable.get_class(parentclass);
            }else{
                STMap.VariableDL var = Symbol_Table.get_variable(expr);
                if (var == null){
                    STMap.ClassST pcl = GlobalSymbolTable.get_class(Symbol_Table.get_parentclass());
                    var = pcl.get_variable(expr);
                    if (var == null) throw new Exception("Error: Unknown variable " + expr);
                }
                cl = GlobalSymbolTable.get_class(var.type);
            }
        }
        /* identifier is a name of a method */
        String id_name = n.f2.accept(this, Symbol_Table);
        STMap.MethodST mthd = cl.get_method(id_name);
        if (mthd == null) throw new Exception("Method " + id_name + " could not be found.");

        /* arguments for calling the method */
        if (n.f4.present()){
             n.f4.accept(this, Symbol_Table);
             if (!this.check_arguments(mthd)) throw new Exception("Error: Arguments don't match at call of " + mthd.name);
        }
        this.IdentifierType = "type";
        return mthd.type;
    }

    /**
    * Grammar production:
    * f0 -> PrimaryExpression()
    * f1 -> "["
    * f2 -> PrimaryExpression()
    * f3 -> "]"
    */
    public String visit(ArrayLookup n, STMap.Level Symbol_Table) throws Exception {
        /* check if primary expression is int array */
        String arrayname = n.f0.accept(this, Symbol_Table);
        STMap.VariableDL var = Symbol_Table.get_variable(arrayname);
        if (var == null){
            var = GlobalSymbolTable.get_class(Symbol_Table.get_parentclass()).get_variable(arrayname);
            if (var == null) throw new Exception("Error: Unknown variable " + arrayname);
        }
        if (var.type != "int[]") throw new Exception("Error: " + arrayname + " is not of type int[]");
        /* check if primary expression of index is int */
        String index = n.f2.accept(this, Symbol_Table);
        if (this.IdentifierType.equals("type")){
            if (!index.equals("int")) throw new Exception("Error: Index must be of type int instead of " + index);
        }else{
            var = Symbol_Table.get_variable(index);
            if (var == null){
                var = GlobalSymbolTable.get_class(Symbol_Table.get_parentclass()).get_variable(index);
                if (var == null) throw new Exception("Error: Unknown variable " + index);
            }
        }
        this.IdentifierType = "type";
        return "int";
    }

    /**
    * Grammar production:
    * f0 -> PrimaryExpression()
    * f1 -> "."
    * f2 -> "length"
    */
    public String visit(ArrayLength n, STMap.Level Symbol_Table) throws Exception {
        String arrayname = n.f0.accept(this, Symbol_Table);
        //check if primary expression is int array
        STMap.VariableDL var = Symbol_Table.get_variable(arrayname);
        if ( var == null ) {
            var = GlobalSymbolTable.get_class(Symbol_Table.get_parentclass()).get_variable(arrayname);
        }
        if (var == null) throw new Exception("Error: Unknown variable " + arrayname);
        if (var.type != "int[]") throw new Exception("Error: " + arrayname + " is not of type int[]");
        this.IdentifierType = "type";
        return "int";
    }

    /**
    * Grammar production:
    * f0 -> NotExpression()
    *       | PrimaryExpression()
    */
    public String visit(Clause n, STMap.Level Symbol_Table) throws Exception {
        String expr = n.f0.accept(this, Symbol_Table);
        return expr;
    }

    /**
    * Grammar production:
    * f0 -> IntegerLiteral()
    *       | TrueLiteral()
    *       | FalseLiteral()
    *       | Identifier()
    *       | ThisExpression()
    *       | ArrayAllocationExpression()
    *       | AllocationExpression()
    *       | BracketExpression()
    */
    public String visit(PrimaryExpression n, STMap.Level Symbol_Table) throws Exception {
        return n.f0.accept(this, Symbol_Table);
    }

    /**
    * Grammar production:
    * f0 -> Expression()
    * f1 -> ExpressionTail()
    */
    public String visit(ExpressionList n, STMap.Level Symbol_Table) throws Exception {
        String expr = n.f0.accept(this, Symbol_Table);
        /* add the first expression to list */
        this.call_args.add(expr);
        n.f1.accept(this, Symbol_Table);
        return null;
    }

    /**
    * Grammar production:
    * f0 -> ( ExpressionTerm() )*
    */
    public String visit(ExpressionTail n, STMap.Level Symbol_Table) throws Exception {
        if (n.f0.present()) n.f0.accept(this, Symbol_Table);
        return null;
    }

    /**
    * Grammar production:
    * f0 -> ","
    * f1 -> Expression()
    */
    public String visit(ExpressionTerm n, STMap.Level Symbol_Table) throws Exception {
        String expr = n.f1.accept(this, Symbol_Table);
        /* add expression to list */
        this.call_args.add(expr);
        return null;
    }

    /**
    * Grammar production:
    * f0 -> "this"
    */
    public String visit(ThisExpression n, STMap.Level Symbol_Table) throws Exception {
        this.IdentifierType = "name";
        return "this";
    }

    /**
    * Grammar production:
    * f0 -> "new"
    * f1 -> "int"
    * f2 -> "["
    * f3 -> Expression()
    * f4 -> "]"
    */
    public String visit(ArrayAllocationExpression n, STMap.Level Symbol_Table) throws Exception {
        String expr = n.f3.accept(this, Symbol_Table);
        /* expression must be of type int */
        if (!expr.equals("int")) throw new Exception("Error: bounds of array must be of type int and not " + expr);
        this.IdentifierType = "type";
        return "int[]";
    }

    /**
    * Grammar production:
    * f0 -> "new"
    * f1 -> Identifier()
    * f2 -> "("
    * f3 -> ")"
    */
    public String visit(AllocationExpression n, STMap.Level Symbol_Table) throws Exception {
        String id_name = n.f1.accept(this, Symbol_Table);
        /* search for identifier class because we are creating an object */
        if(GlobalSymbolTable.exists_class(id_name)) {
            STMap.ClassST id = GlobalSymbolTable.get_class(id_name);
        }else{
            throw new Exception("Error: Cannot create object. There is not type " + id_name);
        }
        this.IdentifierType = "type";
        return id_name;
    }

    /**
    * Grammar production:
    * f0 -> <INTEGER_LITERAL>
    */
    public String visit(IntegerLiteral n, STMap.Level Symbol_Table) throws Exception {
        IdentifierType = "type";
        return "int";
    }

    /**
    * Grammar production:
    * f0 -> "true"
    */
    public String visit(TrueLiteral n, STMap.Level Symbol_Table) throws Exception {
        this.IdentifierType = "type";
        return "boolean";
    }

    /**
    * Grammar production:
    * f0 -> "false"
    */
    public String visit(FalseLiteral n, STMap.Level Symbol_Table) throws Exception {
        this.IdentifierType = "type";
        return "boolean";
    }

    /**
    * Grammar production:
    * f0 -> "("
    * f1 -> Expression()
    * f2 -> ")"
    */
    public String visit(BracketExpression n, STMap.Level Symbol_Table) throws Exception {
        return n.f1.accept(this, Symbol_Table);
    }
}

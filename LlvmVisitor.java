import syntaxtree.*;
import java.util.*;
import java.io.*;
import visitor.GJDepthFirst;


public class LlvmVisitor extends GJDepthFirst <String, STMap.Level> {
    /** LLVM visitor */

    /**
    Global Symbol Table:
    initialized at constructor
    -> contains all classes with their symbol tables
    */
    STMap.SymTable GlobalSymbolTable;

    /**
    Output buffer:
    Used by "emit" function
    -> writes code on the buffer
    */
    FileOutputStream CodeBuffer;

    /**
    Counter for registers, labels
    */
    int reg_lb_counter;

    /**
    I need to know when an primary expression is a
    -type (int-boolean-class name)
    or a
    -name (variable-function name)
    */
    String IdentifierType = null;

    /**
    also register type holds the type (class name)
    of the register returned by primary Expression
    */
    String register_type = null;

    /**
    for printing all types (int and booleans) I have a special variable
    */
    String print_type = null;

    /**
    im using call_args to put together the arguments at function call
    since, ( ExpressionTerm() )* is getting zero or many calls
    and I can't have just a return type
    */
    List<String> call_args = new ArrayList<String>();

    /**
    constructor, using it to initialize my global variables;
    */
    LlvmVisitor(STMap.SymTable st, FileOutputStream buff) {
        GlobalSymbolTable = st;
        CodeBuffer = buff;
        reg_lb_counter = 0;
    }

    /**
    Function to convert types from "java" to llvm
    */
    String decide_type(String type) {
        if (type.equals("int")) {
            return "i32";
        } else if (type.equals("int[]")) {
            return "i32*";
        } else if (type.equals("boolean")) {
            return "i1";
        } else {
            return "i8*";
        }
    }

    /**
    Get a new register
    */
    String acquire_register(){
        String register = "%_" + this.reg_lb_counter;
        this.reg_lb_counter += 1;
        return register;
    }

    /**
    Get a new label id
    */
    int acquire_label(){
        int count = this.reg_lb_counter;
        this.reg_lb_counter += 1;
        return count;
    }

    /**
    Emit : write the bytes of data in file
    if there is error throw an exception
    */
    private void emit(String buffer) {
        try {
            CodeBuffer.write(buffer.getBytes());
        } catch(IOException ex) {
            System.err.println(ex.getMessage());
        }
    }

    /**
    This function is used to create my vtables sorted
    Since vtables must have method in an order of ascending Offsets
    I use this function to sort my HashMap with methods
    to a perfectly sorted by offset List
    (which I iterate later to emit the vtables)
    */
    List<String> Sort_by_offset(HashMap<Integer,STMap.MethodST> methods) {
        List<Integer> Offsets = new ArrayList<Integer>();
        for (Map.Entry<Integer, STMap.MethodST> entry : methods.entrySet()){
            Offsets.add(entry.getKey());
        }
        Collections.sort(Offsets);
        List<String> sorted = new ArrayList<String>();
        for (int offset : Offsets) {
            sorted.add(methods.get(offset).name);
        }
        return sorted;
    }

    /**
    * Grammar production:
    * f0 -> MainClass()
    * f1 -> ( TypeDeclaration() )*
    * f2 -> <EOF>
    */
    public String visit(Goal n, STMap.Level Symbol_Table) throws Exception {
        /* loop for all classes and declare the vtables */
        STMap.ClassST cl;
        STMap.MethodST mthd;
        int num_of_mthds;
        List<String> classes = Symbol_Table.get_all_classes();
        for (String name : classes) {
            cl = GlobalSymbolTable.get_class(name);
            num_of_mthds = cl.get_method_number();
            if (cl.is_mainclass) {
                emit("@." + cl.name + "_vtable = global [0 x i8*] []\n" );
                continue;
            }
            emit("@." + cl.name + "_vtable = global [" + num_of_mthds + " x i8*] [" );
            List<String> methods = Sort_by_offset(cl.get_all_methods());
            boolean first = true;
            for (String mthd_name : methods) {
                if (!first) emit(", ");
                first = false;
                mthd = cl.get_method(mthd_name);
                emit("i8* bitcast (" + decide_type(mthd.type) + " (i8* ");
                for (int i = 0; i < mthd.num_args(); i++){
                    emit(", " + decide_type(mthd.get_arg_type(i)));
                }
                emit(")* ");
                emit("@" + mthd.parentclass + "." + mthd.name + " to i8*)");
            }
            emit("]\n");
            cl.new_vtable(methods);
        }
        emit("\n\n");
        /* declare the help methods */
        emit("declare i8* @calloc(i32, i32)\n" +
            "declare i32 @printf(i8*, ...)\n" +
            "declare void @exit(i32)\n" +
            "\n" +
            "@_cint = constant [4 x i8] c\"%d\\0a\\00\"\n" +
            "@_cOOB = constant [15 x i8] c\"Out of bounds\\0a\\00\"\n" +
            "define void @print_int(i32 %i) {\n" +
                "\t%_str = bitcast [4 x i8]* @_cint to i8*\n" +
                "\tcall i32 (i8*, ...) @printf(i8* %_str, i32 %i)\n" +
                "\tret void\n" +
            "}\n" +
            "\n" +
            "define void @throw_oob() {\n" +
                "\t%_str = bitcast [15 x i8]* @_cOOB to i8*\n" +
                "\tcall i32 (i8*, ...) @printf(i8* %_str)\n" +
                "\tcall void @exit(i32 1)\n" +
                "\tret void\n" +
            "}\n");
            n.f0.accept(this, Symbol_Table);
            if (n.f1.present()) n.f1.accept(this, Symbol_Table);
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
        emit("\ndefine i32 @main(){\n");
        String cl_name = n.f1.accept(this, Symbol_Table);
        String mthd_name = "main";
        if (n.f14.present()) n.f14.accept(this, Symbol_Table.get_class(cl_name).get_method(mthd_name));
        if (n.f15.present()) n.f15.accept(this, Symbol_Table.get_class(cl_name).get_method(mthd_name));
        emit("\n\tret i32 0\n}\n");
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
        String cl_name = n.f1.accept(this, Symbol_Table);
        if (n.f4.present()) n.f4.accept(this, Symbol_Table.get_class(cl_name));
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
        String cl_name = n.f1.accept(this, Symbol_Table);
        if (n.f6.present()) n.f6.accept(this, Symbol_Table.get_class(cl_name));
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
        reg_lb_counter = 0;
        String mthd_type = n.f1.accept(this, Symbol_Table);
        String mthd_name = n.f2.accept(this, Symbol_Table);
        STMap.MethodST mthd = Symbol_Table.get_method(mthd_name);

        mthd_type = decide_type(mthd_type);
        emit("\ndefine " + mthd_type + " @" + Symbol_Table.get_name() + "." + mthd_name + "(i8* %this");
        /* Loop over parameters */
        String arg_type, arg_name;
        for (int i = 0; i < mthd.num_args(); i++){
            arg_type = decide_type(mthd.get_arg_type(i));
            arg_name = mthd.get_arg_name(i);
            emit(", " + arg_type + " %." + arg_name);
        }
        emit(") {\n");
        /* loop again over parameters to allocate space */
        for (int i = 0; i < mthd.num_args(); i++){
            arg_type = decide_type(mthd.get_arg_type(i));
            arg_name = mthd.get_arg_name(i);
            emit("\t%" + arg_name + " = alloca " + arg_type + "\n");
            emit("\tstore " + arg_type + " %." + arg_name + ", " + arg_type + "* %" + arg_name + "\n");
        }
        if (n.f7.present()) n.f7.accept(this, mthd);
        if (n.f8.present()) n.f8.accept(this, mthd);
        /* return expression */
        String return_expr = n.f10.accept(this, mthd);
        emit("\n\tret " + decide_type(mthd.type) + " " + return_expr + "\n}\n");
        return null;
    }

    /**
    * Grammar production:
    * f0 -> Type()
    * f1 -> Identifier()
    * f2 -> ";"
    */
    public String visit(VarDeclaration n, STMap.Level Symbol_Table) throws Exception {
        String var_type = n.f0.accept(this, Symbol_Table);
        /** check if var is either
            1) int-boolean-array, or
            2) class object
        */
        var_type = decide_type(var_type);

        String var_name = n.f1.accept(this, Symbol_Table);
        emit("\t%" + var_name + " = alloca " + var_type + "\n");
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
        STMap.VariableDL var;
        String identifier, expr_register, target, register1, register2, register3, temp_reg;

        expr_register = n.f2.accept(this, Symbol_Table);

        /* search for this identifier */
        identifier = n.f0.accept(this, Symbol_Table);
        temp_reg = null;
        if (Symbol_Table.exists_var(identifier)){
            /* if it exists in this method */
            var = Symbol_Table.get_variable(identifier);
            temp_reg = "%" + var.name;
        }else{
            /* if it is a variable of class */
            var = GlobalSymbolTable.get_class(Symbol_Table.get_parentclass()).get_variable(identifier);
            register1 = acquire_register();
            register2 = acquire_register();
            /* + 8 to offset due to the vtable */
            emit("\t" + register1 + " = getelementptr i8, i8* %this, i32 " + (var.get_offset() + 8) + "\n");
            emit("\t" + register2 + " = bitcast i8* " + register1 + " to " + decide_type(var.type) + "* \n");
            temp_reg = register2;
        }

        emit("\tstore " + decide_type(var.type) + " " + expr_register + ", " + decide_type(var.type) + "* " + temp_reg + "\n\n");
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
        String identifier, index, expr, array;
        String register1, register2, register3, register4, register5, register6, register7;
        int label1, label2, label3;
        STMap.VariableDL var,var2,var3;

        /* search for this identifier */
        identifier = n.f0.accept(this, Symbol_Table);
        if (Symbol_Table.exists_var(identifier)){
            /* if it exists in this method */
            var = Symbol_Table.get_variable(identifier);
            register1 = acquire_register();
            emit("\t" + register1 + " = load " + decide_type(var.type) + ", " + decide_type(var.type) + "* %" + var.name + "\n");
            array = register1;
        }else{
            /* if it is a variable of class */
            var = GlobalSymbolTable.get_class(Symbol_Table.get_parentclass()).get_variable(identifier);
            register1 = acquire_register();
            register2 = acquire_register();
            register3 = acquire_register();
            /* + 8 to offset due to the vtable */
            emit("\t" + register1 + " = getelementptr i8, i8* %this, i32 " + (var.get_offset() + 8) + "\n");
            emit("\t" + register2 + " = bitcast i8* " + register1 + " to " + decide_type(var.type) + "* \n");
            emit("\t" + register3 + " = load " + decide_type(var.type) + ", " + decide_type(var.type) + "* " + register2 + "\n");
            array = register3;
        }

        index = n.f2.accept(this, Symbol_Table);

        label1 = acquire_label();
        label2 = acquire_label();
        label3 = acquire_label();
        register4 = acquire_register();
        register5 = acquire_register();
        register6 = acquire_register();
        register7 = acquire_register();

        /* load array and check for the index if it inside the bounds */
        emit("\t" + register4 + " = load " + decide_type(this.register_type) + ", " + decide_type(this.register_type) + "* " + array + "\n\t" +
            register5 + " = icmp ult i32 " + index + ", " + register4 + "\n\t" +
            "br i1 " + register5 + ", label %oob" + label1 + ", label %oob" + label2 + "\n\t" +
            "\noob" + label1 + ":\n");

        expr = n.f5.accept(this, Symbol_Table);

        /* add 1 because in the first position of the array there is its length */
        emit("\t" + register6 + " = add i32 " + index + ", 1\n\t" +
            register7 + " = getelementptr i32, i32* " + array + ", i32 " + register6 + "\n\t" +
            "store i32 " + expr + ", i32* " + register7 + "\n\t" +
            "br label %oob" + label3 + "\n\n" +
            "oob" + label2 + ":\n\t" +
            "call void @throw_oob()\n\t" +
            "br label %oob" + label3 + "\n\n" +
            "oob" + label3 + ":\n\n");

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
        int label1, label2, label3;
        String expr;

        label1 = acquire_label();
        label2 = acquire_label();
        label3 = acquire_label();

        expr = n.f2.accept(this, Symbol_Table);

        emit("\tbr i1 " + expr + ", label %if" + label1 + ", label %if" + label2 + "\n\n" +
            "if" + label1 + ":\n");
        /* statement 1 */
        n.f4.accept(this, Symbol_Table);
        emit("\tbr label %if" + label3 + "\n\n" +
            "if" + label2 + ":\n");
        /* statement 2 */
        n.f6.accept(this, Symbol_Table);
        emit("\tbr label %if" + label3 + "\n\n" +
            "if" + label3 + ":\n");
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
        int label1, label2, label3;
        String expr;

        label1 = acquire_label();
        label2 = acquire_label();
        label3 = acquire_label();

        /* expr */
        emit("\tbr label %loop" + label1 + "\n\n" +
            "loop" + label1 + ":\n");
        expr = n.f2.accept(this, Symbol_Table);

        emit("\tbr i1 " + expr + ", label %loop" + label2 + ", label %loop" + label3 + "\n\n" +
            "loop" + label2 + ":\n");
        /* statement */
        n.f4.accept(this, Symbol_Table);
        emit("\tbr label %loop" + label1 + "\n\n" +
            "loop" + label3 + ":\n\n");
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
        String expr, register;
        expr = n.f2.accept(this, Symbol_Table);
        if (expr == null) return null;
        if ((print_type != null) && this.print_type.equals("boolean")) {
            register = acquire_register();
            emit("\t" + register + " = zext i1 " + expr + " to i32\n" +
                "\tcall void (i32) @print_int(i32 " + register + ")\n\n");
        } else {
            emit("\tcall void (i32) @print_int(i32 " + expr + ")\n\n");
        }

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
        /* returns the register where the expression result is stored */
        return n.f0.accept(this, Symbol_Table);
    }

    /**
    * Grammar production:
    * f0 -> Clause()
    * f1 -> "&&"
    * f2 -> Clause()
    */
    public String visit(AndExpression n, STMap.Level Symbol_Table) throws Exception {
        String register1, register2, register3;
        int lb1, lb2, lb3, lb4;
        lb1 = acquire_label();
        lb2 = acquire_label();
        lb3 = acquire_label();
        lb4 = acquire_label();
        /* Implementing short circuiting -> if first clause is False no need to check the second clause*/
        register1 = n.f0.accept(this, Symbol_Table);
        emit("\tbr label %andclause" + lb1 + "\n\n");
        /* andclause 1*/
        emit("andclause" + lb1 + ":\n");
        emit("\tbr i1 " + register1 + ", label %andclause" + lb2 + ",label %andclause" + lb4 + "\n\n");
        /* andclause 2*/
        emit("andclause" + lb2 + ":\n");
        register2 = n.f2.accept(this, Symbol_Table);
        emit("br label %andclause" + lb3 + "\n");
        /* andclause 3*/
        emit("\nandclause" + lb3 + ":\n");
        emit("\tbr label %andclause" + lb4 + "\n\n");
        /* andclause 4*/
        register3 = acquire_register();
        emit("andclause" + lb4 + ":\n");
        emit("\t" + register3 + " = phi i1 [ " + register1 + ", %andclause" + lb1 + " ], [ " + register2 + ", %andclause" + lb3 + " ]\n\n");

        this.IdentifierType = "type";
        this.print_type = "boolean";
        return register3;
    }

    /**
    * Grammar production:
    * f0 -> PrimaryExpression()
    * f1 -> "<"
    * f2 -> PrimaryExpression()
    */
    public String visit(CompareExpression n, STMap.Level Symbol_Table) throws Exception {
        String register1, register2, register3;
        register1 = n.f0.accept(this, Symbol_Table);
        register2 = n.f2.accept(this, Symbol_Table);
        register3 = acquire_register();
        emit("\t" + register3 + " = icmp slt i32 " + register1 + ", " + register2 + "\n");

        this.IdentifierType = "type";
        this.print_type = "boolean";
        return register3;
    }

    /**
    * Grammar production:
    * f0 -> PrimaryExpression()
    * f1 -> "+"
    * f2 -> PrimaryExpression()
    */
    public String visit(PlusExpression n, STMap.Level Symbol_Table) throws Exception {
        String register1, register2, register3;
        register1 = n.f0.accept(this, Symbol_Table);
        register2 = n.f2.accept(this, Symbol_Table);
        register3 = acquire_register();
        emit("\t" + register3 + " = add i32 " + register1 + ", " + register2 + "\n");

        this.IdentifierType = "type";
        this.print_type = "int";
        return register3;
    }

    /**
    * Grammar production:
    * f0 -> PrimaryExpression()
    * f1 -> "-"
    * f2 -> PrimaryExpression()
    */
    public String visit(MinusExpression n, STMap.Level Symbol_Table) throws Exception {
        String register1, register2, register3;
        register1 = n.f0.accept(this, Symbol_Table);
        register2 = n.f2.accept(this, Symbol_Table);
        register3 = acquire_register();
        emit("\t" + register3 + " = sub i32 " + register1 + ", " + register2 + "\n");

        this.IdentifierType = "type";
        this.print_type = "int";
        return register3;
    }

    /**
    * Grammar production:
    * f0 -> PrimaryExpression()
    * f1 -> "*"
    * f2 -> PrimaryExpression()
    */
    public String visit(TimesExpression n, STMap.Level Symbol_Table) throws Exception {
        String register1, register2, register3;
        register1 = n.f0.accept(this, Symbol_Table);
        register2 = n.f2.accept(this, Symbol_Table);
        register3 = acquire_register();
        emit("\t" + register3 + " = mul i32 " + register1 + ", " + register2 + "\n");

        this.IdentifierType = "type";
        this.print_type = "int";
        return register3;
    }

    /**
    * Grammar production:
    * f0 -> "!"
    * f1 -> Clause()
    */
    public String visit(NotExpression n, STMap.Level Symbol_Table) throws Exception {
        String register1, register2;
        register1 = n.f1.accept(this, Symbol_Table);
        register2 = acquire_register();
        emit("\t" + register2 + " = xor i1 1, " + register1 + "\n");

        this.IdentifierType = "type";
        this.print_type = "boolean";
        return register2;
    }

    /**
    * Grammar production:
    * f0 -> NotExpression()
    *       | PrimaryExpression()
    */
    public String visit(Clause n, STMap.Level Symbol_Table) throws Exception {
        return n.f0.accept(this, Symbol_Table);
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
    * f0 -> PrimaryExpression()
    * f1 -> "["
    * f2 -> PrimaryExpression()
    * f3 -> "]"
    */
    public String visit(ArrayLookup n, STMap.Level Symbol_Table) throws Exception {
        String register1, register2, register3, register4, expr_reg, ret_reg, var_name;
        int lb1, lb2, lb3;
        STMap.VariableDL var;
        register1 = acquire_register();
        register2 = acquire_register();
        register3 = acquire_register();
        register4 = acquire_register();
        ret_reg = acquire_register();
        lb1 = acquire_label();
        lb2 = acquire_label();
        lb3 = acquire_label();

        /* get the array register */
        expr_reg = n.f0.accept(this, Symbol_Table);

        /* get index and check if it is inside bounds */
        String index = n.f2.accept(this, Symbol_Table);

        emit("\t" + register1 + " = load i32, i32 * " + expr_reg + "\n\t" +
            register2 + " = icmp ult i32 " + index + ", " + register1 + "\n\t" +
            "br i1 " + register2 + ", label %oob" + lb1 + ", label %oob" + lb2 + "\n\n");

        emit("oob" + lb1 + ":\n" +
            "\t" + register3 + " = add i32 " + index + ", 1\n\t" +
            register4 + " = getelementptr i32, i32* " + expr_reg + ", i32 " + register3 + "\n\t" +
            ret_reg + " = load i32, i32* " + register4 + "\n\t" +
            "br label %oob" + lb3 + "\n\n");

        emit("oob" + lb2 + ":\n\t" +
            "call void @throw_oob()\n\t" +
            "br label %oob" + lb3 + "\n\n");

        emit("oob" + lb3 + ":\n\n");

        this.IdentifierType = "type";
        this.print_type = "int";
        return ret_reg;
    }

    /**
    * Grammar production:
    * f0 -> PrimaryExpression()
    * f1 -> "."
    * f2 -> "length"
    */
    public String visit(ArrayLength n, STMap.Level Symbol_Table) throws Exception {
        String register1, register2;

        register2 = acquire_register();
        register1 = n.f0.accept(this, Symbol_Table);

        /* first position of the array contains the length */
        emit("\t" + register2 + " = load i32, i32* " + register1 + "\n");

        this.IdentifierType = "type";
        this.print_type = "int";
        return register2;
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
        String register1, register2, register3, register4, register5, temp_reg, mthd_call_register;
        STMap.VariableDL var;
        STMap.ClassST cl;
        STMap.MethodST mthd;
        String mthd_name;
        int mthd_offset;

        String expr = n.f0.accept(this, Symbol_Table);

        cl = GlobalSymbolTable.get_class(this.register_type);

        mthd_name = n.f2.accept(this, Symbol_Table);
        mthd = cl.get_method(mthd_name);

        /* calculate mthd offset in vtable */
        mthd_offset = cl.find_pos_in_vtable(mthd_name);

        emit("\n\t; " + cl.name + "." + mthd_name + " : " + mthd_offset + "\n");

        register1 = acquire_register();
        register2 = acquire_register();
        register3 = acquire_register();
        register4 = acquire_register();
        register5 = acquire_register();
        mthd_call_register = acquire_register();

        emit("\t" + register1 + " = bitcast i8* " + expr + " to i8***\n\t" +
            register2 + " = load i8**, i8*** " + register1 + "\n\t" +
            register3 + " = getelementptr i8*, i8** " + register2 + ", i32 " + mthd_offset + "\n\t" +
            register4 + " = load i8*, i8** " + register3 + "\n\t" +
            register5 + " = bitcast i8* " + register4 + " to " + decide_type(mthd.type) + " (i8*");

        /* method parameters */
        String parameter_buff = "";
        for (int i = 0; i < mthd.num_args(); i++){
            parameter_buff += ", " + decide_type(mthd.get_arg_type(i));
        }
        parameter_buff += ")*\n";
        emit(parameter_buff);

        /* call arguments */
        String argument_buffer = "";
        n.f4.accept(this, Symbol_Table);
        emit("\t" + mthd_call_register + " = call " + decide_type(mthd.type) + " " + register5 + " (i8* " + expr);
        for (int i = 0; i < this.call_args.size(); i++){
            argument_buffer += ", " + decide_type(mthd.get_arg_type(i)) + " " + call_args.get(i);
        }
        argument_buffer += ")\n\n";
        emit(argument_buffer);

        call_args.clear();

        this.print_type = mthd.type;
        return mthd_call_register;
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
        String expr = n.f0.accept(this, Symbol_Table);
        /* convert simple variables to their registers */
        if (this.IdentifierType.equals("type") || expr.contains("%")) {
            return expr;
        }

        if (expr.equals("%this")) {
            return expr;
        }

        STMap.VariableDL var = null;
        String register, register1, register2, register3;
        register = null;
        register1 = acquire_register();

        /* search in current method */
        if (Symbol_Table.exists_var(expr)) {
            var = Symbol_Table.get_variable(expr);
            emit("\t" + register1 + " = load " + decide_type(var.type) + ", " + decide_type(var.type) + "* %" + var.name + "\n");
            register = register1;
        }else {
            /* else search in parent class of method */
            register2 = acquire_register();
            register3 = acquire_register();
            var = GlobalSymbolTable.get_class(Symbol_Table.get_parentclass()).get_variable(expr);
            /* + 8 to offset due to the vtable */
            emit("\t" + register1 + " = getelementptr i8, i8* %this, i32 " + (var.get_offset() + 8) + "\n" +
                "\t" + register2 + " = bitcast i8* " + register1 + " to " + decide_type(var.type) + "* \n" +
                "\t" + register3 + " = load " + decide_type(var.type) + ", " + decide_type(var.type) + "* " + register2 + "\n");
            register = register3;
        }

        this.print_type = var.type;
        this.register_type = var.type;
        return register;
    }

    /**
    * Grammar production:
    * f0 -> Expression()
    * f1 -> ExpressionTail()
    */
    public String visit(ExpressionList n, STMap.Level Symbol_Table) throws Exception {
        String expr = n.f0.accept(this, Symbol_Table);
        /* add the first expression to argument list */
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
        /* add expression to argument list */
        this.call_args.add(expr);
        return null;
    }

    /**
    * Grammar production:
    * f0 -> "this"
    */
    public String visit(ThisExpression n, STMap.Level Symbol_Table) throws Exception {
        this.IdentifierType = "name";
        /**
        I need to know what %this means ->
        so I used this variable to pass it on the parent node who calls this
        */
        this.register_type = Symbol_Table.get_parentclass();
        return "%this";
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
        int lb1, lb2;
        String register1,register2,register3;
        lb1 = acquire_label();
        lb2 = acquire_label();

        register1 = n.f3.accept(this, Symbol_Table);
        register2 = acquire_register();

        emit("\t" + register2 + " = icmp slt i32 " + register1 + ", 0\n" +
            "\tbr i1 " + register2 + ", label %arr_alloc" + lb1 + ", label %arr_alloc" + lb2 + "\n\n");
        /* array alloc 1 in case of invalid bounds*/
        emit("arr_alloc" + lb1 + ":\n");
        emit("\tcall void @throw_oob()\n\tbr label %arr_alloc" + lb2 + "\n\n");
        /* array alloc 2 */
        String register4, register5, register6;
        register3 = acquire_register();
        register4 = acquire_register();
        register5 = acquire_register();
        emit("arr_alloc" + lb2 + ":\n\t");
        /* storing array size from register 1 to the first pos of the array */
        emit(register3 + " = add i32 " + register1 + ", 1\n\t" +
            register4 + " = call i8* @calloc(i32 4, i32 " + register3 + ")\n\t" +
            register5 + " = bitcast i8* " + register4 + " to i32*\n\t" +
            "store i32 " + register1 + ", i32* " + register5 + "\n");

        this.register_type = "int[]";
        this.IdentifierType = "type";
        return register5;
    }

    /**
    * Grammar production:
    * f0 -> "new"
    * f1 -> Identifier()
    * f2 -> "("
    * f3 -> ")"
    */
    public String visit(AllocationExpression n, STMap.Level Symbol_Table) throws Exception {
        String register1, register2, register3, identifier;
        register1 = acquire_register();
        register2 = acquire_register();
        register3 = acquire_register();
        identifier = n.f1.accept(this, Symbol_Table);
        STMap.ClassST cl = GlobalSymbolTable.get_class(identifier);
        /* + 8 for vtable pointer */
        emit("\t" + register1 + " = call i8* @calloc (i32 1, i32 " + (cl.get_offset() + 8) + ")\n\t" +
            register2 + " = bitcast i8* " + register1 + " to i8***\n\t" +
            register3 + " = getelementptr [" + cl.get_method_number() + " x i8*], [" + cl.get_method_number() + " x i8*]* @." + cl.name + "_vtable, i32 0, i32 0\n\t" +
            "store i8** " + register3 + ", i8*** " + register2 + "\n");

        this.register_type = cl.name;
        this.IdentifierType = "type";
        return register1;
    }

    /**
    * Grammar production:
    * f0 -> <INTEGER_LITERAL>
    */
    public String visit(IntegerLiteral n, STMap.Level Symbol_Table) throws Exception {
        String integer = n.f0.toString();
        this.IdentifierType = "type";
        this.register_type = "int";
        this.print_type = "int";
        return integer;
    }

    /**
    * Grammar production:
    * f0 -> "true"
    */
    public String visit(TrueLiteral n, STMap.Level Symbol_Table) throws Exception {
        this.IdentifierType = "type";
        this.register_type = "boolean";
        this.print_type = "boolean";
        return "1";
    }

    /**
    * Grammar production:
    * f0 -> "false"
    */
    public String visit(FalseLiteral n, STMap.Level Symbol_Table) throws Exception {
        this.IdentifierType = "type";
        this.register_type = "boolean";
        this.print_type = "boolean";
        return "0";
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

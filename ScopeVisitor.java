import syntaxtree.*;
import java.util.*;
import visitor.GJDepthFirst;

public class ScopeVisitor extends GJDepthFirst <String, STMap.Level> {

    /**
        This is my stack with all the class variables - methods
    */
    Stack<STMap.Level> GlobalSymbolTable;
    /**
        Since there are no inner classes a map with all the Classes
        saves me from a lot of trouble, when checking for superclasses
        and virtual methods.
    */
    STMap.SymTable ClassesSymbolTable;

    /**
        Initializing the stack and map from Main
    */
    ScopeVisitor(Stack<STMap.Level> gst, STMap.SymTable classes){
        GlobalSymbolTable = gst;
        ClassesSymbolTable = classes;
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
        STMap.ClassST cl = new STMap.ClassST();
        cl.name = n.f1.f0.toString();
        cl.is_mainclass = true;
        Symbol_Table.add_class(cl);
        STMap.MethodST mthd = new STMap.MethodST();
        mthd.name = "main";
        mthd.type = "void";
        mthd.parentclass = cl.name;
        STMap.VariableDL var = new STMap.VariableDL();
        var.type = "String[]";
        var.parentname = "main";
        var.name = n.f11.accept(this, var);
        mthd.add_variable(var);
        cl.add_method(mthd);
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
        STMap.ClassST cl = new STMap.ClassST();
        cl.name = n.f1.f0.toString();
        if (Symbol_Table.exists_class(cl.name)) throw new Exception( "Class " + cl.name + " already exists.");

        Symbol_Table.add_class(cl);
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
        STMap.ClassST cl = new STMap.ClassST();
        cl.name = n.f1.accept(this, cl);
        if (Symbol_Table.exists_class(cl.name)) throw new Exception( "Class " + cl.name + " already exists.");

        STMap.ClassST pcl;
        String spclname = n.f3.accept(this, Symbol_Table);
        if (!Symbol_Table.exists_class(spclname)) throw new Exception( "Super Class " + spclname + "does not exist.");

        if (cl.name.equals(spclname)) throw new Exception("Class and Super Class have the same name.");

        pcl = ClassesSymbolTable.get_class(spclname);
        cl.parentclass = Symbol_Table.get_name();
        cl.superclass = pcl.name;
        cl.offset = pcl.offset;
        cl.mthd_offset = pcl.mthd_offset;
        Symbol_Table.add_class(cl);
        if (n.f5.present()) n.f5.accept(this, cl);
        if (n.f6.present()) n.f6.accept(this, cl);
        /* fix scopes */
        Symbol_Table.get_class(pcl.name).merge_scopes(cl);
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
        STMap.MethodST mthd = new STMap.MethodST();
        mthd.name = n.f2.accept(this, mthd);
        mthd.type = n.f1.accept(this, mthd);
        mthd.parentclass = Symbol_Table.get_name();
        mthd.offset = Symbol_Table.get_mthd_offset();
        if (Symbol_Table.exists_method(mthd.name)) throw new Exception("Method " + mthd.name + " is already declared in this scope of class " + Symbol_Table.get_name() + ".");
        Symbol_Table.add_method(mthd);
        if (n.f4.present()) n.f4.accept(this, mthd);

        String superclass = Symbol_Table.get_superclass();
        /** If superclass is null there is no inheritance
            -> so no virtuality on the method.
            Else if it is NOT null, I have to check
            if there is overriding.
        */
        if (superclass != null) {
            STMap.ClassST SuperClass = ClassesSymbolTable.get_class(superclass);
            /** If there is inheritance, we need to check for methods
                to have overiding there should be a method
                with the same name at SuperClass
            */
            if (SuperClass.exists_method(mthd.name)) mthd.overiding = true;
        }
        /* if there is overiding, no need to add this function again in the symbol table */
        if (!mthd.overiding){
            Symbol_Table.increment_mthd_offset();
            GlobalSymbolTable.push(mthd);
        }
        if (n.f7.present()) n.f7.accept(this, mthd);
        if (n.f8.present()) n.f8.accept(this, mthd);
        return null;
    }

    /**
    * Grammar production:
    * f0 -> Type()
    * f1 -> Identifier()
    * f2 -> ";"
    */
    public String visit(VarDeclaration n, STMap.Level Symbol_Table) throws Exception {
        STMap.VariableDL var = new STMap.VariableDL();
        var.type = n.f0.accept(this, var);
        var.name = n.f1.accept(this, var);
        if (Symbol_Table.exists_var(var.name)) throw new Exception("Variable " + var.name + " already exists in this scope.");
        var.parentname = Symbol_Table.get_name();
        var.offset = Symbol_Table.get_offset();
        Symbol_Table.add_variable(var);
        if (Symbol_Table.get_type().equals("class")){
            if (var.type.equals("int") || var.type.equals("boolean")){
                Symbol_Table.increment_offset(var.type);
            }else{
                Symbol_Table.increment_offset("pointer");
            }
            GlobalSymbolTable.push(var);
        }
        return null;
    }

    /**
    * Grammar production:
    * f0 -> Type()
    * f1 -> Identifier()
    */
    public String visit(FormalParameter n, STMap.Level Symbol_Table) throws Exception {
        STMap.VariableDL var = new STMap.VariableDL();
        var.name = n.f1.accept(this, var);
        var.type = n.f0.accept(this, var);
        if (Symbol_Table.exists_var(var.name)) throw new Exception("Variable " + var.name + " already exists in this scope.");
        var.parentname = Symbol_Table.get_name();
        Symbol_Table.add_variable(var);
        Symbol_Table.add_arg_type(var.type);
        Symbol_Table.add_arg_name(var.name);
        return null;
    }


    /**
    * Grammar production:
    * f0 -> <IDENTIFIER>
    */
    public String visit(Identifier n, STMap.Level Symbol_Table) throws Exception {
        String var = n.f0.toString();
        return var;
    }

    /**
    * Grammar production:
    * f0 -> "int"
    */
    public String visit(IntegerType n, STMap.Level Symbol_Table) throws Exception{
        String var = n.f0.toString();
        return var;
    }

    /**
    * Grammar production:
    * f0 -> "boolean"
    */
    public String visit(BooleanType n, STMap.Level Symbol_Table) throws Exception{
        String var = n.f0.toString();
        return var;
    }

    /**
    * Grammar production:
    * f0 -> "int"
    * f1 -> "["
    * f2 -> "]"
    */
    public String visit(ArrayType n, STMap.Level Symbol_Table) throws Exception {
        return "int[]";
    }
}

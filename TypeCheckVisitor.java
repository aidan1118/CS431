package semant;

import ast.*;
import visitor.*;
import util.*;

import java.util.*;

/** Visitor class for typechecking the AST */
public class TypeCheckVisitor extends Visitor {
    private static HashSet<String> reservedNames =
        new HashSet<String>(Arrays.asList("this", "super", "null"));
    private static HashSet<String> primitives =
        new HashSet<String>(Arrays.asList("boolean", "int"));
    
    private ErrorHandler errorHandler;
    /** Class map to use for typechecking */
    private Hashtable<String, ClassTreeNode> classMap;
    private ClassTreeNode curClass;

    private boolean isInLoop = false;

    /** TypeCheckVisitor constructor
      * @param varSymbolTable VarSymbolTable for typechecking
      * */
    public TypeCheckVisitor(Hashtable<String, ClassTreeNode> classMap,
        ErrorHandler errorHandler) {
        this.classMap = classMap;
        this.errorHandler = errorHandler;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(Class_ node) {
        curClass = classMap.get(node.getName());
        MemberList memberList = node.getMemberList();
        Iterator<ASTNode> iter = memberList.getIterator();

        while (iter.hasNext()) {
            iter.next().accept(this);
        }

        return null;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(Field node) {
        if (node.getInit() == null) {
            return null;
        }
        
        Expr init = node.getInit();
        init.accept(this);
        String type = node.getType();
        String initType = init.getExprType();

        if (primitives.contains(type) || primitives.contains(initType)) {
            if (!initType.equals(type)) {
                errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                    "Primitive types do not match");
                return null;
            }

            return null;
        }
        else {
            if (initType == "null") {
                return null;
            }

            if (type.endsWith("[]")) {
                type = type.substring(0, type.length() - 2);

                if (initType.endsWith("[]")) {
                    initType = initType.substring(0, initType.length() - 2);
                }
                
                if (type.equals(initType)) {
                    return null;
                }
            }

            ClassTreeNode parent = classMap.get(initType);
            while (parent != null) {
                if (parent.getName().equals(type)) {
                    return null;
                }

                parent = parent.getParent();
            }
        }

        errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
            "Reference types do not match");
        return null;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(Method node) {
        String type = node.getReturnType();
        FormalList formalList = node.getFormalList();
        StmtList stmtList = node.getStmtList();
        SymbolTable varSymbolTable = curClass.getVarSymbolTable();
        varSymbolTable.enterScope();

        Iterator<ASTNode> formalIter = formalList.getIterator();
        while (formalIter.hasNext()) {
            formalIter.next().accept(this);
        }

        Iterator<ASTNode> stmtIter = stmtList.getIterator();
        while (stmtIter.hasNext()) {
            ASTNode stmt = stmtIter.next();
            Object result = stmt.accept(this);

            if (stmt instanceof ReturnStmt && result instanceof String) {
                String ret = (String)result;
                
                if (type.equals("void") || primitives.contains(type)) {
                    if (!type.equals(ret)) {
                        errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                            "Primitive types do not match");
                        varSymbolTable.exitScope();
                        return null;
                    }
                }
                else {
                    if (ret.equals("null")) {
                        varSymbolTable.exitScope();
                        return null;
                    }

                    boolean found = false;
                    ClassTreeNode parent = classMap.get(ret);

                    while (parent != null) {
                        if (parent.getName().equals(type)) {
                            found = true;
                            break;
                        }

                        parent = parent.getParent();
                    }

                    if (!found) {
                        errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                            "Reference types do not match");
                        varSymbolTable.exitScope();
                        return null;
                    }
                }
            }
        }

        varSymbolTable.exitScope();
        return null;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(Formal node) {
        String name = node.getName();
        if (reservedNames.contains(name)) {
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Formal name is reserved");
            return null;
        }

        SymbolTable varSymbolTable = curClass.getVarSymbolTable();
        int curScope = varSymbolTable.getCurrScopeLevel();
        if (varSymbolTable.lookup(name) != null &&
            varSymbolTable.getScopeLevel(name) == curScope) {
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Multiply declared formal");
            return null;
        }

        String type = node.getType();
        String check = type;
        if (check != null && check.endsWith("[]")) {
            check = check.substring(0, check.length() - 2);
        }

        if (check == null || 
            (!classMap.containsKey(check) && !primitives.contains(check))) {
            type = "Object";
        }
        
        varSymbolTable.add(name, type);
        return null;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(DeclStmt node) {
        String name = node.getName();
        if (reservedNames.contains(name)) {
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Declaration name is reserved");
            return null;
        }

        SymbolTable varSymbolTable = curClass.getVarSymbolTable();
        if (varSymbolTable.lookup(name) != null) {
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Multiply declared variable");
            return null;
        }
        varSymbolTable.add(name, node.getType());

        String type = node.getType();
        if (type == null) {
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Missing declaration type");
            return null;
        }

        Expr init = node.getInit();
        init.accept(this);
        String initType = init.getExprType();

        String checkType = type;
        String checkInit = initType;

        if (checkType.endsWith("[]") && checkInit.endsWith("[]")) {
            checkType = checkType.substring(0, checkType.length() - 2);
            checkInit = checkInit.substring(0, checkInit.length() - 2);
        }

        if ((primitives.contains(checkType) || primitives.contains(checkInit)) &&
            !initType.equals(type)) {
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Declaration types do not match");
            return null;
        }

        return null;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(ExprStmt node) {
        Expr expr = node.getExpr();
        expr.accept(this);

        if (!(expr instanceof AssignExpr ||
            expr instanceof ArrayAssignExpr ||
            expr instanceof NewExpr ||
            expr instanceof DispatchExpr ||
            expr instanceof UnaryIncrExpr ||
            expr instanceof UnaryDecrExpr)) {
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Invalid expression type");
            return null;
        }

        return null;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(IfStmt node) {
        Expr pred = node.getPredExpr();
        pred.accept(this);

        if (!pred.getExprType().equals("boolean")) {
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Predicate type is not boolean");
            return null;
        }

        node.getThenStmt().accept(this);
        node.getElseStmt().accept(this);
        return null;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(WhileStmt node) {
        Expr pred = node.getPredExpr();
        pred.accept(this);
        if (!pred.getExprType().equals("boolean")) {
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Predicate type is not boolean");
            return null;
        }

        boolean wasInLoop = isInLoop;
        isInLoop = true;
        node.getBodyStmt().accept(this);
        isInLoop = wasInLoop;

        return null;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(ForStmt node) {
        Expr pred = node.getPredExpr();

        if (pred != null) {
            pred.accept(this);
            
            if (!pred.getExprType().equals("boolean")) {
                errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                    "Predicate type is not boolean");
                return null;
            }
        }

        Expr init = node.getInitExpr();
        if (init != null) {
            init.accept(this);
        }

        Expr update = node.getUpdateExpr();
        if (update != null) {
            update.accept(this);
        }

        boolean wasInLoop = isInLoop;
        isInLoop = true;
        node.getBodyStmt().accept(this);
        isInLoop = wasInLoop;

        return null;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(BlockStmt node) {
        SymbolTable varSymbolTable = curClass.getVarSymbolTable();
        varSymbolTable.enterScope();

        Iterator<ASTNode> iter = node.getStmtList().getIterator();
        while (iter.hasNext()) {
            iter.next().accept(this);
        }

        varSymbolTable.exitScope();
        return null;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(ReturnStmt node) {
        Expr expr = node.getExpr();
        if (expr == null) {
            return "void";
        }

        expr.accept(this);
        String type = expr.getExprType();

        if (type.equals("void")) {
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Return type is void");
            return "Object";
        }

        return type;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(DispatchExpr node) {
        Expr ref = node.getRefExpr();
        ref.accept(this);
        String refType = ref.getExprType();
        
        if (primitives.contains(refType) || refType.equals("void")) {
            node.setExprType("Object");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Invalid reference type");
            return "Object";
        }

        ClassTreeNode parent = classMap.get("Object");
        Method destMethod = null;
        if (!refType.endsWith("[]")) {
            parent = classMap.get(refType);
        }
        
        if (parent != null) {
            SymbolTable methodSymbolTable = parent.getMethodSymbolTable();
            Object temp = methodSymbolTable.lookup(node.getMethodName());

            if (temp != null && temp instanceof Method) {
                destMethod = (Method)temp;
            }
        }

        if (destMethod == null) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Missing dispatch method");
            return "null";
        }

        FormalList sourceList = destMethod.getFormalList();
        Iterator<ASTNode> sourceIter = sourceList.getIterator();
        ExprList actualList = node.getActualList();
        Iterator<ASTNode> actualIter = actualList.getIterator();

        if (sourceList.getSize() != actualList.getSize()) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Invalid number of arguments");
            return "null";
        }

        while (sourceIter.hasNext() && actualIter.hasNext()) {
            Formal source = (Formal)sourceIter.next();
            String sourceType = source.getType();
            Expr actual = (Expr)actualIter.next();
            actual.accept(this);
            String actualType = actual.getExprType();

            if (actualType.endsWith("[]") && sourceType.endsWith("[]")) {
                actualType = actualType.substring(0, actualType.length() - 2);
                sourceType = sourceType.substring(0, sourceType.length() - 2);
            }
            
            if (actualType.equals("void") || (primitives.contains(actualType) &&
                !sourceType.equals(actualType))) {
                node.setExprType("null");
                errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                    "Invalid argument primitive type");
                return "null";
            }

            if (!primitives.contains(actualType) && actualType != "null") {
                ClassTreeNode actualClass = classMap.get(actualType);
                boolean found = false;

                while (actualClass != null) {
                    if (actualClass.getName().equals(sourceType)) {
                        found = true;
                        break;
                    }

                    actualClass = actualClass.getParent();
                }

                if (!found) {
                    node.setExprType("null");
                    errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                        "Invalid argument reference type");
                    return "null";
                }
            }
        }

        node.setExprType(destMethod.getReturnType());
        return node.getExprType();
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(CastExpr node) {
        String type = node.getType();
        String check = type;
        if (check.endsWith("[]")) {
            check = check.substring(0, check.length() - 2);
        }

        if (type.endsWith("[]")) {
            if (!classMap.containsKey(check) && !primitives.contains(check)) {
                node.setExprType("Object");
                errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                    "Undeclared cast type");
                return "Object";
            }
        }
        else if (!classMap.containsKey(check)) {
            node.setExprType("Object");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Undeclared cast type");
            return "Object";
        }

        Expr expr = node.getExpr();
        expr.accept(this);
        String exprType = expr.getExprType();
        if (primitives.contains(exprType)) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Invalid cast type");
            return "null";
        }

        if (type.endsWith("[]") && exprType.equals("Object")) {
            node.setExprType(type);
            node.setUpCast(false);
            return type;
        }

        if (type.equals("Object") && exprType.endsWith("[]")) {
            node.setExprType(type);
            node.setUpCast(true);
            return type;
        }

        String checkType = type;
        String checkExpr = exprType;

        if (checkType.endsWith("[]") && checkExpr.endsWith("[]")) {
            checkType = checkType.substring(0, checkType.length() - 2);
            checkExpr = checkExpr.substring(0, checkExpr.length() - 2);
        }

        if (primitives.contains(checkType) && checkType.equals(checkExpr)) {
            node.setExprType(type);
            node.setUpCast(true);
            return type;
        }

        ClassTreeNode parent = classMap.get(checkExpr);
        while (parent != null) {
            if (parent.getName().equals(checkType)) {
                node.setExprType(type);
                node.setUpCast(true);
                return type;
            }

            parent = parent.getParent();
        }

        parent = classMap.get(checkType);
        while (parent != null) {
            if (parent.getName().equals(checkExpr)) {
                node.setExprType(type);
                node.setUpCast(false);
                return type;
            }

            parent = parent.getParent();
        }

        node.setExprType("null");
        errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
            "Invalid cast type");
        return "null";
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(InstanceofExpr node) {
        String type = node.getType();
        if (!type.endsWith("[]") && !classMap.containsKey(type)) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Invalid reference type");
            return "null";
        }

        Expr expr = node.getExpr();
        expr.accept(this);
        String exprType = expr.getExprType();
        if (exprType.equals("void") || primitives.contains(exprType)) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Invalid desired type");
            return "null";
        }

        node.setExprType("boolean");
        return "boolean";
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(NewExpr node) {
        String type = node.getType();
        if (classMap.containsKey(type)) {
            node.setExprType(type);
            return type;
        }

        node.setExprType("Object");
        return "Object";
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(NewArrayExpr node) {
        Expr size = node.getSize();
        size.accept(this);
        String sizeType = size.getExprType();
        if (!sizeType.equals("int")) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Array size is not an int");
            return "null";
        }

        node.setExprType(node.getType() + "[]");
        return node.getExprType();
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(AssignExpr node) {
        Expr expr = node.getExpr();
        expr.accept(this);

        String type = null;
        String exprType = expr.getExprType();
        String ref = node.getRefName();
        String name = node.getName();
        ClassTreeNode parent = curClass;

        if (ref != null) {
            if (ref.equals("super")) {
                parent = parent.getParent();
            }
            else if (!ref.equals("this")) {
                node.setExprType("null");
                errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                    "Invalid reference name");
                return "null";
            }
        }
        
        while (parent != null) {
            SymbolTable varSymbolTable = parent.getVarSymbolTable();
            Object temp = varSymbolTable.lookup(name);
            
            if (temp != null && temp instanceof String) {
                type = (String)temp;
                break;
            }

            parent = parent.getParent();
        }

        if (type == null) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Invalid init type");
            return "null";
        }

        if (exprType.equals("void") || !type.equals(exprType)) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Reference and init types do not match");
            return "null";
        }
        
        node.setExprType(type);
        return type;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(ArrayAssignExpr node) {
        Expr index = node.getIndex();
        index.accept(this);
        if (!index.getExprType().equals("int")) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Array index is not an int");
            return "null";
        }
    
        Expr expr = node.getExpr();
        expr.accept(this);  // Type of RHS expression
    
        String exprType = expr.getExprType();  // e.g., "Main"
        String ref = node.getRefName();
        String name = node.getName();
        ClassTreeNode parent = curClass;
    
        if (ref != null) {
            if (ref.equals("super")) {
                parent = parent.getParent();
            } else if (!ref.equals("this")) {
                node.setExprType("null");
                errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                    "Invalid reference type");
                return "null";
            }
        }
    
        SymbolTable varSymbolTable = parent.getVarSymbolTable();
        Object temp = varSymbolTable.lookup(name);
        String arrayType = null;
        if (temp instanceof String) {
            arrayType = (String)temp;
        }
    
        if (arrayType == null || !arrayType.endsWith("[]")) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Invalid array variable type");
            return "null";
        }
    
        String elementType = arrayType.substring(0, arrayType.length() - 2);
        if (exprType.equals("void")) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Cannot assign void to array element");
            return "null";
        }
    
        // Prefer to annotate with the RHS type if it is a subclass of the array's element type
        if (primitives.contains(elementType)) {
            if (!elementType.equals(exprType)) {
                errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                    "Primitive type mismatch in array assignment");
                node.setExprType("null");
                return "null";
            }
            node.setExprType(elementType);
            return elementType;
        } else {
            // Check if exprType is a subclass of elementType
            ClassTreeNode rhsClass = classMap.get(exprType);
            while (rhsClass != null) {
                if (rhsClass.getName().equals(elementType)) {
                    node.setExprType(exprType);  // ← Use the more specific RHS type here!
                    return exprType;
                }
                rhsClass = rhsClass.getParent();
            }
        }
    
        node.setExprType("null");
        errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
            "Reference and init types do not match in array assignment");
        return "null";
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(UnaryDecrExpr node) {
        Expr expr = node.getExpr();
        if (!(expr instanceof VarExpr || expr instanceof ArrayExpr)) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Invalid expression type");
            return "null";
        }
        
        expr.accept(this);
        String type = expr.getExprType();
        String oper = node.getOperandType();
        
        if (!type.equals(oper)) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Type does not match expected");
            return "null";
        }

        node.setExprType(type);
        return type;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(UnaryIncrExpr node) {
        Expr expr = node.getExpr();
        if (!(expr instanceof VarExpr || expr instanceof ArrayExpr)) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Invalid expression type");
            return "null";
        }
        
        expr.accept(this);
        String type = expr.getExprType();
        String oper = node.getOperandType();
        
        if (!type.equals(oper)) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Type does not match expected");
            return "null";
        }

        node.setExprType(type);
        return type;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(UnaryNegExpr node) {
        Expr expr = node.getExpr();
        expr.accept(this);
        String type = expr.getExprType();
        String oper = node.getOperandType();
        
        if (!type.equals(oper)) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Type does not match expected");
            return "null";
        }

        node.setExprType(type);
        return type;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(UnaryNotExpr node) {
        Expr expr = node.getExpr();
        expr.accept(this);
        String type = expr.getExprType();
        String oper = node.getOperandType();
        
        if (!type.equals(oper)) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Type does not match expected");
            return "null";
        }

        node.setExprType(type);
        return type;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(BinaryArithDivideExpr node) {
        Expr lhs = node.getLeftExpr();
        lhs.accept(this);
        String lhsType = lhs.getExprType();

        Expr rhs = node.getRightExpr();
        rhs.accept(this);
        String rhsType = rhs.getExprType();

        String operand = node.getOperandType();
        String operator = node.getOpType();

        if (!lhsType.equals(operand) || !rhsType.equals(operand)) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Type does not match expected");
            return "null";
        }

        node.setExprType(operator);
        return operator;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(BinaryArithMinusExpr node) {
        Expr lhs = node.getLeftExpr();
        lhs.accept(this);
        String lhsType = lhs.getExprType();

        Expr rhs = node.getRightExpr();
        rhs.accept(this);
        String rhsType = rhs.getExprType();

        String operand = node.getOperandType();
        String operator = node.getOpType();

        if (!lhsType.equals(operand) || !rhsType.equals(operand)) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Type does not match expected");
            return "null";
        }

        node.setExprType(operator);
        return operator;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(BinaryArithModulusExpr node) {
        Expr lhs = node.getLeftExpr();
        lhs.accept(this);
        String lhsType = lhs.getExprType();

        Expr rhs = node.getRightExpr();
        rhs.accept(this);
        String rhsType = rhs.getExprType();

        String operand = node.getOperandType();
        String operator = node.getOpType();

        if (!lhsType.equals(operand) || !rhsType.equals(operand)) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Type does not match expected");
            return "null";
        }

        node.setExprType(operator);
        return operator;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(BinaryArithPlusExpr node) {
        Expr lhs = node.getLeftExpr();
        lhs.accept(this);
        String lhsType = lhs.getExprType();

        Expr rhs = node.getRightExpr();
        rhs.accept(this);
        String rhsType = rhs.getExprType();

        String operand = node.getOperandType();
        String operator = node.getOpType();

        if (!lhsType.equals(operand) || !rhsType.equals(operand)) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Type does not match expected");
            return "null";
        }

        node.setExprType(operator);
        return operator;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(BinaryArithTimesExpr node) {
        Expr lhs = node.getLeftExpr();
        lhs.accept(this);
        String lhsType = lhs.getExprType();

        Expr rhs = node.getRightExpr();
        rhs.accept(this);
        String rhsType = rhs.getExprType();

        String operand = node.getOperandType();
        String operator = node.getOpType();

        if (!lhsType.equals(operand) || !rhsType.equals(operand)) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Type does not match expected");
            return "null";
        }

        node.setExprType(operator);
        return operator;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(BinaryCompEqExpr node) {
        Expr lhs = node.getLeftExpr();
        lhs.accept(this);
        String lhsType = lhs.getExprType();

        Expr rhs = node.getRightExpr();
        rhs.accept(this);
        String rhsType = rhs.getExprType();

        if (primitives.contains(lhsType) || primitives.contains(rhsType)) {
            if (!lhsType.equals(rhsType)) {
                node.setExprType("null");
                errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                    "Operand primitive types do not match");
                return "null";
            }
        }
        else if (lhsType != "null" && rhsType != "null") {
            boolean valid = false;

            ClassTreeNode parent = classMap.get(lhsType);
            while (parent != null) {
                if (parent.getName().equals(rhsType)) {
                    valid = true;
                    break;
                }

                parent = parent.getParent();
            }

            parent = classMap.get(rhsType);
            while (parent != null) {
                if (parent.getName().equals(lhsType)) {
                    valid = true;
                    break;
                }

                parent = parent.getParent();
            }

            if (!valid) {
                node.setExprType("null");
                errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                    "Operand reference types do not match");
                return "null";
            }
        }

        String operator = node.getOpType();
        node.setExprType(operator);
        return operator;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(BinaryCompGeqExpr node) {
        Expr lhs = node.getLeftExpr();
        lhs.accept(this);
        String lhsType = lhs.getExprType();

        Expr rhs = node.getRightExpr();
        rhs.accept(this);
        String rhsType = rhs.getExprType();

        String operand = node.getOperandType();
        String operator = node.getOpType();

        if (!lhsType.equals(operand) || !rhsType.equals(operand)) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Type does not match expected");
            return "null";
        }

        node.setExprType(operator);
        return operator;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(BinaryCompGtExpr node) {
        Expr lhs = node.getLeftExpr();
        lhs.accept(this);
        String lhsType = lhs.getExprType();

        Expr rhs = node.getRightExpr();
        rhs.accept(this);
        String rhsType = rhs.getExprType();

        String operand = node.getOperandType();
        String operator = node.getOpType();

        if (!lhsType.equals(operand) || !rhsType.equals(operand)) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Type does not match expected");
            return "null";
        }

        node.setExprType(operator);
        return operator;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(BinaryCompLeqExpr node) {
        Expr lhs = node.getLeftExpr();
        lhs.accept(this);
        String lhsType = lhs.getExprType();

        Expr rhs = node.getRightExpr();
        rhs.accept(this);
        String rhsType = rhs.getExprType();

        String operand = node.getOperandType();
        String operator = node.getOpType();

        if (!lhsType.equals(operand) || !rhsType.equals(operand)) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Type does not match expected");
            return "null";
        }

        node.setExprType(operator);
        return operator;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(BinaryCompLtExpr node) {
        Expr lhs = node.getLeftExpr();
        lhs.accept(this);
        String lhsType = lhs.getExprType();

        Expr rhs = node.getRightExpr();
        rhs.accept(this);
        String rhsType = rhs.getExprType();

        String operand = node.getOperandType();
        String operator = node.getOpType();

        if (!lhsType.equals(operand) || !rhsType.equals(operand)) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Type does not match expected");
            return "null";
        }

        node.setExprType(operator);
        return operator;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(BinaryCompNeExpr node) {
        Expr lhs = node.getLeftExpr();
        lhs.accept(this);
        String lhsType = lhs.getExprType();

        Expr rhs = node.getRightExpr();
        rhs.accept(this);
        String rhsType = rhs.getExprType();

        if (primitives.contains(lhsType) || primitives.contains(rhsType)) {
            if (!lhsType.equals(rhsType)) {
                node.setExprType("null");
                errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                    "Operand primitive types do not match");
                return "null";
            }
        }
        else if (lhsType != "null" && rhsType != "null") {
            boolean valid = false;

            ClassTreeNode parent = classMap.get(lhsType);
            while (parent != null) {
                if (parent.getName().equals(rhsType)) {
                    valid = true;
                    break;
                }

                parent = parent.getParent();
            }

            parent = classMap.get(rhsType);
            while (parent != null) {
                if (parent.getName().equals(lhsType)) {
                    valid = true;
                    break;
                }

                parent = parent.getParent();
            }

            if (!valid) {
                node.setExprType("null");
                errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                    "Operand reference types do not match");
                return "null";
            }
        }

        String operator = node.getOpType();
        node.setExprType(operator);
        return operator;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(BinaryLogicAndExpr node) {
        Expr lhs = node.getLeftExpr();
        lhs.accept(this);
        String lhsType = lhs.getExprType();

        Expr rhs = node.getRightExpr();
        rhs.accept(this);
        String rhsType = rhs.getExprType();

        String operand = node.getOperandType();
        String operator = node.getOpType();

        if (!lhsType.equals(operand) || !rhsType.equals(operand)) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Type does not match expected");
            return "null";
        }

        node.setExprType(operator);
        return operator;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(BinaryLogicOrExpr node) {
        Expr lhs = node.getLeftExpr();
        lhs.accept(this);
        String lhsType = lhs.getExprType();

        Expr rhs = node.getRightExpr();
        rhs.accept(this);
        String rhsType = rhs.getExprType();

        String operand = node.getOperandType();
        String operator = node.getOpType();

        if (!lhsType.equals(operand) || !rhsType.equals(operand)) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Type does not match expected");
            return "null";
        }

        node.setExprType(operator);
        return operator;
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(VarExpr node) {
        String name = node.getName();
        Expr ref = node.getRef();
        
        if (ref != null) {
            ref.accept(this);
            String type = ref.getExprType();

            if (ref instanceof VarExpr) {
                String refName = ((VarExpr)ref).getName();
                String check = node.getName();
                ClassTreeNode parent = curClass;
                
                if (refName.equals("super")) {
                    parent = parent.getParent();
                }
                else if (!refName.equals("this")) {
                    check = refName;
                }

                SymbolTable varSymbolTable = parent.getVarSymbolTable();
                Object temp = varSymbolTable.lookup(check);
                if (temp != null && temp instanceof String) {
                    type = (String)temp;
                }
            }

            if (type == null) {
                node.setExprType("Object");
                return "Object";
            }

            if (type.endsWith("[]")) {
                if (!name.equals("length")) {
                    node.setExprType("null");
                    errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                        "Invalid array field");
                    return "null";
                }

                node.setExprType("int");
                return "int";
            }

            node.setExprType(type);
            return type;
        }

        if (name.equals("this")) {
            node.setExprType(curClass.getName());
            return node.getExprType();
        }

        if (name.equals("super")) {
            ClassTreeNode parent = curClass.getParent();
            if (parent == null) {
                node.setExprType("null");
                errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                    "Undeclared field reference");
                return "null";
            }

            node.setExprType(parent.getName());
            return node.getExprType();
        }

        if (name.equals("null")) {
            node.setExprType("null");
            return "null";
        }

        SymbolTable varSymbolTable = curClass.getVarSymbolTable();
        Object temp = varSymbolTable.lookup(name);
        if (temp != null && temp instanceof String) {
            node.setExprType((String)temp);
            return node.getExprType();
        }

        node.setExprType("Object");
        return "Object";
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(ArrayExpr node) {
        Expr index = node.getIndex();
        index.accept(this);
        if (!index.getExprType().equals("int")) {
            node.setExprType("null");
            errorHandler.register(errorHandler.SEMANT_ERROR, curClass.getASTNode().getFilename(), node.getLineNum(),
                "Array size is not an int");
            return "null";
        }

        String name = node.getName();
        Expr ref = node.getRef();

        if (ref != null) {
            ref.accept(this);
            if (ref instanceof VarExpr) {
                String refName = ((VarExpr)ref).getName();
                String check = node.getName();
                ClassTreeNode parent = curClass;
                
                if (refName.equals("super")) {
                    parent = parent.getParent();
                }
                else if (!refName.equals("this")) {
                    check = refName;
                }

                String type = null;

                if (parent != null) {
                    SymbolTable varSymbolTable = parent.getVarSymbolTable();
                    Object temp = varSymbolTable.lookup(check);
                    if (temp != null && temp instanceof String) {
                        type = (String)temp;
                    }
                }
                
                if (type == null) {
                    node.setExprType("Object");
                    return "Object";
                }

                if (type.endsWith("[]")) {
                    node.setExprType(type.substring(0, type.length() - 2));
                    return node.getExprType();
                }

                node.setExprType("Object");
                return "Object";
            }
        }

        SymbolTable varSymbolTable = curClass.getVarSymbolTable();
        Object temp = varSymbolTable.lookup(name);
        if (temp != null && temp instanceof String) {
            String type = (String)temp;
            if (type.endsWith("[]")) {
                node.setExprType(type.substring(0, type.length() - 2));
                return node.getExprType();
            }
        }

        node.setExprType("Object");
        return "Object";
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(ConstBooleanExpr node) {
        node.setExprType("boolean");
        return "boolean";
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(ConstIntExpr node) {
        node.setExprType("int");
        return "int";
    }
    
    /** Typecheck AST node
      * @param node AST node
      * @return null (returns value to satisfy compiler)
      * */
    public Object visit(ConstStringExpr node) {
        node.setExprType("String");
        return "String";
    }
}
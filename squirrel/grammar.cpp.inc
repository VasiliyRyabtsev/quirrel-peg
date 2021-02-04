static const char *grammar = R"(
    Statements <- Statement*
    Statement <- (
        ReturnStatement / IfStmt / ForStmt / ForeachStmt / WhileStmt / DoWhileStmt / BlockStmt /
        BreakStmt / ContinueStmt / ThrowStmt / TryCatchStmt /
        'local' LocalDeclStatement / VarModifyStmt / SlotModifyStmt /
        Expression / ';'
    )

    ReturnStatement <- 'return' Expression
    BlockStmt <- '{' Statements '}'
    BreakStmt <- 'break'
    ContinueStmt <- 'continue'

    LocalDeclStatement <- 'function' LocalFuncDeclStmt / LocalVarsDeclStmt / 'class' LocalClassDeclStmt
    LocalVarDeclStmt <- IDENTIFIER '=' Expression / IDENTIFIER
    LocalVarsDeclStmt <- LocalVarDeclStmt (',' LocalVarDeclStmt)*
    LocalFuncDeclStmt <- IDENTIFIER FuncDecl
    LocalClassDeclStmt <- IDENTIFIER ClassInit
    
    FuncDecl <- '(' FuncParams ')' Statement
    FuncParams <- IDENTIFIER? (',' IDENTIFIER)*
    Expression <- BinaryOpExpr / PrefixedExpr
    BinaryOpExpr <- PrefixedExpr (BINARY_OP PrefixedExpr)* {
                            precedence
                            L ??
                            L ||
                            L && in
                            L ^
                            L &
                            L == != <=>
                            L < <= > >= instanceof
                            L << >> >>>
                            L + -
                            L / * %

    }
    PrefixedExpr    <- (LOADROOT RootSlotGet / Factor ) (FunctionCall / SlotGet / SlotNamedGet)*
    Factor          <- FLOAT / INTEGER / BOOLEAN / NULL / STRING_LITERAL / IDENTIFIER /
                        ArrayInit / TableInit / 'class' ClassInit / UnaryOperation / '(' Expression ')'

    UnaryOperation  <- UnaryOperator PrefixedExpr
    UnaryOperator   <- <'!' / '~' / '-' / 'typeof' / 'resume' / 'clone' >

    FunctionCall    <- '(' ArgValues ')'
    SlotGet         <- '[' Expression ']'
    SlotNamedGet    <- '.' IDENTIFIER
    RootSlotGet     <- IDENTIFIER
    ArgValues       <- Expression? (','? Expression)*
    ArrayInit       <- '[' ArgValues ']'

    TableInit       <- '{'  (TableInitItem ','? )* '}'
    TableInitItem   <- ((IDENTIFIER / ('[' Expression ']') ) '=' Expression) / IDENTIFIER

    ClassInit       <- ClassExtends '{'  (ClassInitItem ';'? )* '}'
    ClassExtends    <- ('extends' Expression)?
    ClassInitItem   <- ((IDENTIFIER / ('[' Expression ']') ) '=' Expression / 'function' IDENTIFIER FuncDecl / Constructor)
    Constructor     <- 'function'? 'constructor' FuncDecl

    VarModifyStmt   <- IDENTIFIER VarModifyOp Expression
    VarModifyOp     <- '=' / '+=' / '-='
    #SlotModifyStmt  <- PrefixedExpr '[' Expression ']' SlotModifyOp Expression
    SlotModifyStmt  <- Factor '[' Expression ']' SlotModifyOp Expression
    SlotModifyOp    <- '=' / '<-'

    IfStmt      <- 'if' '(' Expression ')' Statement ('else' Statement)?

    ForStmt     <- 'for' '(' ForInit ';' ForCond ';' ForAction ')' Statement
    ForInit     <- ('local' LocalVarsDeclStmt)?
    ForCond     <- Expression?
    ForAction   <- Expression? (',' Expression)*

    ForeachStmt <- 'foreach' '(' IDENTIFIER (',' IDENTIFIER)? 'in' Expression ')' Statement

    WhileStmt      <- 'while' '(' Expression ')' Statement
    DoWhileStmt    <- 'do' Statement 'while' '(' Expression ')'

    ThrowStmt   <- 'throw' Expression
    TryCatchStmt <- 'try' Statement 'catch' '(' IDENTIFIER ')' Statement

    INTEGER     <- < [-+]? [0-9]+ >
    FLOAT       <- < [-+]?[0-9]* '.'? [0-9]+([eE][-+]?[0-9]+)? / ['-+']?[0-9]+ '.' [0-9]* >
    BOOLEAN     <- < 'true' | 'false' >
    NULL        <- 'null'
    STRING_LITERAL <- '"' < ([^"] / '""')* > '"'
    IDENTIFIER  <- < !KEYWORD [a-zA-Z_][a-zA-Z_0-9]* / 'this' >
    BINARY_OP   <- '??' / '||' / '&&' / '^' / '&' /
                    '==' / '!=' / '<=>' / '<='/ '>=' / '<<' / '>>' / '>>>' / '<' / '>' /
                    '+' / '-' / '/' / '*' / '%' /
                    'in' / 'instanceof'
    LOADROOT    <- '::'

    KEYWORD <- 'while' / 'do' / 'if' / 'else' / 'break' / 'continue' / 'return' / 'null' / 'function' /
        'local' / 'for' / 'foreach' / 'in' / 'typeof' / 'base' / 'delete' / 'try' / 'catch' / 'throw' /
        'clone' / 'yield' / 'resume' / 'switch' / 'case' / 'default' / 'this' / 'class' / 'extends' /
        'constructor' / 'instanceof' / 'true' / 'false' / 'static' / 'enum' / 'const' / '__LINE__' / '__FILE__'
        / 'rawcall' / 'global' / 'not'

    EOL <- '\r\n' / '\n' / '\r'
    EOF <- !.

    MultilineComment <- '/*' (!'*/' .)* '*/'
    SingleLineComment <- '//' (!(EOL / EOF) .)* (EOL / EOF)

    %whitespace <- ([ \t\r\n] / MultilineComment / SingleLineComment)*
    %word       <- [a-zA-Z_][a-zA-Z_0-9]*
)";

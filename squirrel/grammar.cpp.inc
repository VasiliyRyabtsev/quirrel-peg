static const char *grammar = R"(
    Statements <- Statement*
    Statement <- (
        ReturnStatement / YieldStatement /
        IfStmt / ForStmt / ForeachStmt / WhileStmt / DoWhileStmt / SwitchStmt / BlockStmt /
        BreakStmt / ContinueStmt / ThrowStmt / TryCatchStmt /
        'local' LocalDeclStatement /
        FuncAtThisStmt / ClassAtThisStmt /
        Expression / ';'
    )

    ReturnStatement <- 'return' Expression?
    YieldStatement <- 'yield' Expression
    BlockStmt <- '{' Statements '}'
    BreakStmt <- 'break'
    ContinueStmt <- 'continue'

    LocalDeclStatement <- 'function' LocalFuncDeclStmt / LocalVarsDeclStmt / 'class' LocalClassDeclStmt
    LocalVarDeclStmt <- IDENTIFIER '=' Expression / IDENTIFIER
    LocalVarsDeclStmt <- LocalVarDeclStmt (',' LocalVarDeclStmt)*
    LocalFuncDeclStmt <- IDENTIFIER FuncDecl
    LocalClassDeclStmt <- IDENTIFIER ClassInit
    
    FuncDecl <- '(' FuncParams ')' Statement
    FuncParam <- !FuncDefParam IDENTIFIER
    FuncDefParam <- IDENTIFIER '=' Expression
    VarParams <- '...'
    FuncParams <- (FuncParam ','?)* (FuncDefParam ','?)* VarParams?

    Expression <- BinaryOpExpr TernarySelect?

    BinaryOpExpr <- ChainExpr (BINARY_OP ChainExpr)* {
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

    ChainExpr  <- PrefixedExpr (ExprOperator Expression)?

    PrefixedExpr    <- (LOADROOT RootSlotGet / Factor) (FunctionCall / SlotGet / SlotNamedGet)*
    ExprOperator    <- '=' / '<-' / '+=' / '-='

    Factor          <- FLOAT / INTEGER / BOOLEAN / NULL / STRING_LITERAL / VERBATIM_STRING / StrInterp / IDENTIFIER /
                        ArrayInit / TableInit / 'class' ClassInit / UnaryOperation / PreIncrDecr / '(' Expression ')'

    TernarySelect   <- '?' Expression ':' Expression

    UnaryOperation  <- UnaryOperator ChainExpr
    UnaryOperator   <- !IncrDecrOp <'!' / '~' / '-' / 'typeof' / 'resume' / 'clone' >

    PreIncrDecr     <- IncrDecrOp ChainExpr
    IncrDecrOp      <- '++' / '--'

    FunctionCall    <- '(' ArgValues ')'
    SlotGet         <- '[' Expression ']'
    SlotNamedGet    <- '.' IDENTIFIER
    SlotSet         <- '[' Expression ']'
    SlotNamedSet    <- '.' IDENTIFIER
    RootSlotGet     <- IDENTIFIER

    ArgValues       <- Expression? (','? Expression)*
    ArrayInit       <- '[' ArgValues ']'

    TableInit       <- '{'  (TableInitItem ','? )* '}'
    TableInitItem   <- ((IDENTIFIER / ('[' Expression ']') ) '=' Expression) / IDENTIFIER / 'function' IDENTIFIER FuncDecl

    ClassInit       <- ClassExtends '{'  (ClassInitItem ';'? )* '}'
    ClassExtends    <- ('extends' Expression)?
    ClassInitItem   <- ((IDENTIFIER / ('[' Expression ']') ) '=' Expression / 'function' IDENTIFIER FuncDecl / Constructor)
    Constructor     <- 'function'? 'constructor' FuncDecl

    IfStmt      <- 'if' '(' Expression ')' Statement ('else' Statement)?

    ForStmt     <- 'for' '(' ForInit ';' ForCond ';' ForCommaExpr ')' Statement
    ForInit     <- ('local' LocalVarsDeclStmt / ForCommaExpr)?
    ForCond     <- Expression?
    ForCommaExpr<- Expression? (',' Expression)*

    ForeachStmt <- 'foreach' '(' IDENTIFIER (',' IDENTIFIER)? 'in' Expression ')' Statement

    WhileStmt      <- 'while' '(' Expression ')' Statement
    DoWhileStmt    <- 'do' Statement 'while' '(' Expression ')'

    SwitchStmt  <- 'switch' '(' Expression ')' '{' SwitchCase* SwitchDefault? '}'
    SwitchCase  <- 'case' Expression ':' Statements
    SwitchDefault <- 'default' ':' Statements

    ThrowStmt   <- 'throw' Expression
    TryCatchStmt <- 'try' Statement 'catch' '(' IDENTIFIER ')' Statement

    FuncAtThisStmt <- 'function' IDENTIFIER FuncDecl
    ClassAtThisStmt <- 'class' IDENTIFIER ClassInit

    INTEGER     <- < [-+]? [0-9]+ >
    FLOAT       <- < [-+]?[0-9]* '.'? [0-9]+([eE][-+]?[0-9]+)? / ['-+']?[0-9]+ '.' [0-9]* >
    BOOLEAN     <- < 'true' | 'false' >
    NULL        <- 'null'
    STRING_LITERAL <- <'"' < (!'"' .)* > '"'>
    VERBATIM_STRING <- <'@"' < (!'"' . / '""')* > '"'>
    IDENTIFIER  <- < !KEYWORD [a-zA-Z_][a-zA-Z_0-9]* / 'this' >
    BINARY_OP   <- !IncrDecrOp <'??' / '||' / '&&' / '^' / '&' /
                    '==' / '!=' / '<=>' / '<='/ '>=' / '<<' / '>>' / '>>>' / '<' / '>' /
                    '+' / '-' / '/' / '*' / '%' /
                    'in' / 'instanceof'>
    LOADROOT    <- '::'

    KEYWORD <- 'while' / 'do' / 'if' / 'else' / 'break' / 'continue' / 'return' / 'null' / 'function' /
        'local' / 'for' / 'foreach' / 'in' / 'typeof' / 'base' / 'delete' / 'try' / 'catch' / 'throw' /
        'clone' / 'yield' / 'resume' / 'switch' / 'case' / 'default' / 'this' / 'class' / 'extends' /
        'constructor' / 'instanceof' / 'true' / 'false' / 'static' / 'enum' / 'const' / '__LINE__' / '__FILE__'
        / 'rawcall' / 'global' / 'not'

    StrInterp        <- '$"' (StrInterpExpr / StrInterpChars)* '"'
    StrInterpExpr    <- '{' Expression '}'
    StrInterpChars   <- ('\\"' / !'"' !'{' .)+

    EOL <- '\r\n' / '\n' / '\r'
    EOF <- !.

    MultilineComment <- '/*' (!'*/' .)* '*/'
    SingleLineComment <- '//' (!(EOL / EOF) .)* (EOL / EOF)

    %whitespace <- ([ \t\r\n] / MultilineComment / SingleLineComment)*
    %word       <- [a-zA-Z_][a-zA-Z_0-9]*
)";

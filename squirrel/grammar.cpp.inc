static const char *grammar = R"(
    Statements <- Statement*
    Statement <- (
        Directive /
        ReturnStatement / YieldStatement /
        IfStmt / ForStmt / ForeachStmt / WhileStmt / DoWhileStmt / SwitchStmt / BlockStmt /
        BreakStmt / ContinueStmt / ThrowStmt / TryCatchStmt /
        ConstStmt / EnumStmt /
        'local' LocalDeclStatement /
        FuncAtThisStmt / ClassAtThisStmt /
        Expression / ';'
    )

    ReturnStatement <-  `[ 'return' ]` [ \t]* (~EOL / Expression?) ~%whitespace
    YieldStatement <- 'yield' Expression
    BlockStmt <- '{' Statements '}'
    BreakStmt <- 'break'
    ContinueStmt <- 'continue'

    LocalDeclStatement <- 'function' LocalFuncDeclStmt / LocalVarsDeclStmt / 'class' LocalClassDeclStmt
                            / LocalTblDestructuring / LocalArrDestructuring
    LocalVarDeclStmt <- IDENTIFIER '=' Expression / IDENTIFIER
    LocalVarsDeclStmt <- LocalVarDeclStmt (',' LocalVarDeclStmt)*
    LocalFuncDeclStmt <- IDENTIFIER FuncDecl
    LocalClassDeclStmt <- IDENTIFIER ClassInit
    LocalTblDestructuring <- '{' LocalVarsDeclStmt '}' '=' Expression
    LocalArrDestructuring <- '[' LocalVarsDeclStmt ']' '=' Expression

    ConstStmt <- ConstModifier 'const' IDENTIFIER '=' SCALAR
    ConstModifier <- <'global'>?
    EnumStmt <- ConstModifier 'enum' IDENTIFIER '{' SEQ(EnumEntry, ',') '}'
    EnumEntry <- IDENTIFIER ('=' SCALAR)?

    FuncDecl <- '(' FuncParams ')' Statement
    FuncParam <- !FuncDefParam IDENTIFIER
    FuncDefParam <- IDENTIFIER '=' Expression
    VarParams <- '...'
    FuncParams <- (FuncParam ','?)* (FuncDefParam ','?)* VarParams?
    LambdaDecl <- '@' '(' FuncParams ')' Expression

    Expression <- BinaryOpExpr TernarySelect?

    BinaryOpExpr <- ChainExpr (INFIX_OP ChainExpr)* {
                            precedence
                            L ??
                            L ||
                            L &&
                            L |
                            L ^
                            L &
                            L == != <=>
                            L < <= > >= in instanceof
                            L << >> >>>
                            L + -
                            L / * %
    }

    ChainExpr  <- PrefixedExpr (ExprOperator Expression / IncrDecrOp)?

    PrefixedExpr    <- (LOADROOT RootSlotGet / Factor)
                        (
                            FunctionCall / SlotGet / SlotNamedGet /
                            FunctionNullCall / SlotNullGet / SlotNamedNullGet
                        )*

    ExprOperator    <- '=' / '<-' / '+=' / '-='

    Factor          <- FLOAT / INTEGER / BOOLEAN / NULL / STRING_LITERAL / VERBATIM_STRING / StrInterp / IDENTIFIER /
                        ArrayInit / TableInit / 'class' ClassInit / FactorFunc /
                        UnaryOperation / PreIncrDecr / '(' Expression ')'
    FactorFunc      <- 'function' IDENTIFIER? FuncDecl / LambdaDecl

    TernarySelect   <- '?' Expression ':' Expression

    UnaryOperation  <- UnaryOperator ChainExpr
    UnaryOperator   <- !IncrDecrOp <'!' / '~' / '-' / 'typeof' / 'resume' / 'clone' >

    PreIncrDecr     <- IncrDecrOp ChainExpr
    IncrDecrOp      <- '++' / '--'

    FunctionCall    <- '(' ArgValues ')'
    SlotGet         <- '[' Expression ']'
    SlotNamedGet    <- '.' IDENTIFIER
    FunctionNullCall<- '?(' ArgValues ')'
    SlotNullGet     <- '?[' Expression ']'
    SlotNamedNullGet<- '?.' IDENTIFIER
    SlotSet         <- '[' Expression ']'
    SlotNamedSet    <- '.' IDENTIFIER
    RootSlotGet     <- IDENTIFIER

    ArgValues       <- (Expression ','?)*
    ArrayInit       <- '[' ArgValues ']'

    TableInit       <- '{'  (TableInitItem ','? )* '}'
    TableInitItem   <- (IDENTIFIER / ('[' Expression ']') ) '=' Expression /
                        STRING_LITERAL ':' Expression /
                        IDENTIFIER /
                        'function' IDENTIFIER FuncDecl

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

    INTEGER     <- < '0x'[0-9a-fA-F]+ / [-+]?[0-9]+ / [']("\\'" / [^'])['] >
    FLOAT       <- < [-+]?[0-9]* '.'? [0-9]+([eE][-+]?[0-9]+)? / [-+]?[0-9]+ '.' [0-9]* >
    BOOLEAN     <- < 'true' / 'false' >
    NULL        <- 'null'
    STRING_LITERAL <- <'"' < (!'"' .)* > '"'>
    VERBATIM_STRING <- <'@"' < (!'"' . / '""')* > '"'>
    IDENTIFIER  <- < !KEYWORD [a-zA-Z_][a-zA-Z_0-9]* / 'this' >
    INFIX_OP   <- !IncrDecrOp <'??' / '||' / '&&' / '|' / '^' / '&' /
                    '==' / '!=' / '<=>' / '<='/ '>=' / '<<' / '>>>' / '>>' / '<' / '>' /
                    '+' / '-' / '/' / '*' / '%' /
                    'in' / 'instanceof'>
    LOADROOT    <- '::'

    KEYWORD <- 'while' / 'do' / 'if' / 'else' / 'break' / 'continue' / 'return' / 'null' / 'function' /
        'local' / 'for' / 'foreach' / 'in' / 'typeof' / 'base' / 'delete' / 'try' / 'catch' / 'throw' /
        'clone' / 'yield' / 'resume' / 'switch' / 'case' / 'default' / 'this' / 'class' / 'extends' /
        'constructor' / 'instanceof' / 'true' / 'false' / 'static' / 'enum' / 'const' / '__LINE__' / '__FILE__'
        / 'rawcall' / 'global' / 'not'

    SCALAR <- INTEGER / FLOAT / BOOLEAN / NULL / STRING_LITERAL / VERBATIM_STRING

    StrInterp        <- `['$"']` (StrInterpExpr / StrInterpChars)* '"'
    StrInterpExpr    <- '{' Expression `[ '}' ]`
    StrInterpChars   <- ('\\"' / !'"' !'{' .)+

    Directive <- '#' <(!(EOL / ' ' / '\t') .)*>   #[ \t]* (EOL)

    SEQ(ITEM, SEP) <- ITEM (~SEP? ITEM)*
    OPT_SEQ(ITEM, SEP) <- ITEM? (~SEP? ITEM)*

    EOL <- '\r\n' / '\n' / '\r' / !.

    BlockComment <- '/*' (!'*/' .)* '*/'
    LineComment <- '//' (!EOL .)* &EOL

    %whitespace <- ([ \t\r\n] / BlockComment / LineComment)*
    %word       <- [a-zA-Z_][a-zA-Z_0-9]*
)";

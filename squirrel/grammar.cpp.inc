static const char *grammar = R"(
    Statements <- ( Statement (';' / EOL)* )*
    Statement <- (
        ReturnStatement / IfStmt / ForStmt / ForeachStmt / BlockStmt /
        'local' LocalDeclStatement / VarModifyStmt / SlotModifyStmt /
        Expression
    )

    ReturnStatement <- 'return' Expression
    BlockStmt <- '{' Statements '}'
    LocalDeclStatement <- 'function' LocalFuncDeclStmt / LocalVarsDeclStmt
    LocalVarDeclStmt <- IDENTIFIER '=' Expression / IDENTIFIER
    LocalVarsDeclStmt <- LocalVarDeclStmt (',' LocalVarDeclStmt)*
    LocalFuncDeclStmt <- IDENTIFIER '(' FuncParams ')' Statement
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
    Factor          <- FLOAT / INTEGER / BOOLEAN / NULL / STRING_LITERAL / IDENTIFIER / ArrayInit / TableInit / '(' Expression ')'

    FunctionCall    <- '(' ArgValues ')'
    SlotGet         <- '[' Expression ']'
    SlotNamedGet    <- '.' IDENTIFIER
    RootSlotGet     <- IDENTIFIER
    ArgValues       <- Expression? (','? Expression)*
    ArrayInit       <- '[' ArgValues ']'

    TableInit       <- '{'  (TableInitItem ','? )* '}'
    TableInitItem   <- ((IDENTIFIER / ('[' Expression ']') ) '=' Expression) / IDENTIFIER

    VarModifyStmt   <- IDENTIFIER VarModifyOp Expression
    VarModifyOp     <- '=' / '+=' / '-='
    #SlotModifyStmt  <- PrefixedExpr '[' Expression ']' SlotModifyOp Expression
    SlotModifyStmt  <- Factor '[' Expression ']' SlotModifyOp Expression
    SlotModifyOp    <- '=' / '<-'

    IfStmt      <- 'if' '(' Expression ')' ('{' Statements '}' / Statement) ('else' ('{' Statements '}' / Statement))?

    ForStmt     <- 'for' '(' ForInit ';' ForCond ';' ForAction ')' ('{' Statements '}' / ';')
    ForInit     <- ('local' LocalVarsDeclStmt)?
    ForCond     <- Expression?
    ForAction   <- Expression? (',' Expression)*

    ForeachStmt <- 'foreach' '(' IDENTIFIER (',' IDENTIFIER)? 'in' Expression ')' Statement

    INTEGER     <- < [-+]? [0-9]+ >
    FLOAT       <- < [-+]?[0-9]* '.'? [0-9]+([eE][-+]?[0-9]+)? / ['-+']?[0-9]+ '.' [0-9]* >
    BOOLEAN     <- < 'true' | 'false' >
    NULL        <- 'null'
    STRING_LITERAL <- '"' < ([^"] / '""')* > '"'
    IDENTIFIER  <- < !KEYWORD [a-zA-Z_][a-zA-Z_0-9]* >
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

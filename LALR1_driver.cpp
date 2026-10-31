#include <algorithm>
#include <iostream>
#include <map>
#include <memory>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

/*
 * Driver LALR(1) - Practica 6
 *
 * Gramatica
 *   0. S' -> S
 *   1. S  -> L = R
 *   2. S  -> R
 *   3. L  -> * R
 *   4. L  -> id
 *   5. R  -> L
 *
 * Formato de entrada: Una cadena por linea, con tokens separados por espacios.
 *   Un identificador puede llevar su lexema, id:x
 *   El $ final es opcional (se agrega si falta)
 *
 * Salida por cadena: Traza de la pila, estado final, validez y AST en texto.
 */

namespace
{

    struct Token
    {
        std::string kind;
        std::string lexeme;
    };

    // Nodo del AST, solo aparecen asignaciones, desreferencias e identificadores
    struct AstNode
    {
        std::string label;
        std::string value;
        std::vector<std::unique_ptr<AstNode>> children;
    };

    enum class ActionKind
    {
        Shift,
        Reduce,
        Accept
    };

    struct Action
    {
        ActionKind kind;
        int value = 0; // Estado destino (shift) o numero de regla (reduce)
    };

    struct Production
    {
        std::string lhs;
        std::vector<std::string> rhs;
    };

    // Action y Goto guardan solo las celdas definidas, una celda vacia es error
    using ActionTable = std::map<int, std::map<std::string, Action>>;
    using GotoTable = std::map<int, std::map<std::string, int>>;

    struct Tables
    {
        ActionTable action;
        GotoTable goTo;
        std::vector<std::string> problems; // Conflictos o errores de captura
    };

    struct TraceRow
    {
        std::string step;
        std::string stack;
        std::string input;
        std::string action;
    };

    const std::vector<std::string> kTerminals = {"id", "=", "*", "$"};
    const std::vector<std::string> kNonTerminals = {"S", "L", "R"};

    // La posicion en el vector es el numero de regla (r0-r5)
    const std::vector<Production> kProductions = {
        {"S'", {"S"}},
        {"S", {"L", "=", "R"}},
        {"S", {"R"}},
        {"L", {"*", "R"}},
        {"L", {"id"}},
        {"R", {"L"}}};

    
    const std::map<int, std::string> kStateNames = {};

    std::string stateLabel(int state)
    {
        const auto it = kStateNames.find(state);
        return it == kStateNames.end() ? std::to_string(state) : it->second;
    }

    bool contains(const std::vector<std::string> &list, const std::string &symbol)
    {
        return std::find(list.begin(), list.end(), symbol) != list.end();
    }

    std::string productionText(int rule)
    {
        const auto &production = kProductions.at(static_cast<std::size_t>(rule));
        std::string out = production.lhs + " ->";
        for (const auto &symbol : production.rhs)
            out += " " + symbol;
        return out;
    }

    std::string actionText(const Action &action)
    {
        switch (action.kind)
        {
        case ActionKind::Shift:
            return "s" + stateLabel(action.value);
        case ActionKind::Reduce:
            return "r" + std::to_string(action.value);
        case ActionKind::Accept:
            break;
        }
        return "acc";
    }

    void setAction(Tables &tables, int state, const std::string &terminal,
                   const Action &value)
    {
        // Una celda con dos acciones distintas es un conflicto. La tabla LALR(1)
        // de esta gramatica no debe tener ninguno, asi que se reporta como error.
        auto &row = tables.action[state];
        const auto existing = row.find(terminal);
        if (existing == row.end())
        {
            row.emplace(terminal, value);
            return;
        }
        if (existing->second.kind != value.kind ||
            existing->second.value != value.value)
        {
            tables.problems.push_back(
                "Conflicto en ACTION[" + stateLabel(state) + "][" + terminal +
                "]: " + actionText(existing->second) + " / " + actionText(value));
        }
    }

    Tables buildTables()
    {
        Tables tables;
        auto s = [&](int state, const char *terminal, int destination)
        {
            setAction(tables, state, terminal, {ActionKind::Shift, destination});
        };
        auto r = [&](int state, int rule, const std::vector<std::string> &lookaheads)
        {
            for (const auto &terminal : lookaheads)
                setAction(tables, state, terminal, {ActionKind::Reduce, rule});
        };
        auto acc = [&](int state)
        {
            setAction(tables, state, "$", {ActionKind::Accept, 0});
        };
        auto g = [&](int state, const char *nonTerminal, int destination)
        {
            tables.goTo[state][nonTerminal] = destination;
        };

       
        // Tabla LALR(1)
        //
        //   s(estado, "terminal", destino);        
        //   r(estado, regla, {"t1", "t2"});        
        //   acc(estado);                           
        //   g(estado, "NoTerminal", destino);      
        //
        // A diferencia de SLR(1), cada reduce lleva solo los lookaheads de su
        // item LR(1), no todo el Follow del no terminal. Por eso el estado 2
        // reduce R -> L solo con $ y desplaza con '=' sin conflicto.

        // Action
        s(0, "id", 5);
        s(0, "*", 4);

        acc(1);

        s(2, "=", 6);
        r(2, 5, {"$"});

        r(3, 2, {"$"});

        s(4, "id", 5);
        s(4, "*", 4);

        r(5, 4, {"=", "$"});

        s(6, "id", 5);
        s(6, "*", 4);

        r(7, 3, {"=", "$"});

        r(8, 5, {"=", "$"});

        r(9, 1, {"$"});

        // Goto
        g(0, "S", 1);
        g(0, "L", 2);
        g(0, "R", 3);

        g(4, "L", 8);
        g(4, "R", 7);

        g(6, "L", 8);
        g(6, "R", 9);

        return tables;
    }

    void validateTables(Tables &tables)
    {
        // Detecta errores de captura como destinos sin fila, reglas o simbolos fuera de la gramatica
        const auto exists = [&](int state)
        { return tables.action.count(state) != 0; };
        const int lastRule = static_cast<int>(kProductions.size()) - 1;

        for (const auto &row : tables.action)
        {
            for (const auto &cell : row.second)
            {
                const std::string where =
                    "ACTION[" + stateLabel(row.first) + "][" + cell.first + "]";
                if (!contains(kTerminals, cell.first))
                    tables.problems.push_back(where + ": terminal desconocido");
                if (cell.second.kind == ActionKind::Shift && !exists(cell.second.value))
                    tables.problems.push_back(where + ": el estado destino " + stateLabel(cell.second.value) + " no tiene fila en ACTION");
                if (cell.second.kind == ActionKind::Reduce &&
                    (cell.second.value < 1 || cell.second.value > lastRule))
                    tables.problems.push_back(where + ": r" + std::to_string(cell.second.value) + " no es una regla valida para reducir");
            }
        }

        for (const auto &row : tables.goTo)
        {
            for (const auto &cell : row.second)
            {
                const std::string where =
                    "GOTO[" + stateLabel(row.first) + "][" + cell.first + "]";
                if (!exists(row.first))
                    tables.problems.push_back(where + ": El estado no tiene fila en ACTION");
                if (!contains(kNonTerminals, cell.first))
                    tables.problems.push_back(where + ": No terminal desconocido");
                if (!exists(cell.second))
                    tables.problems.push_back(where + ": El estado destino " + stateLabel(cell.second) + " no tiene fila en ACTION");
            }
        }
    }

    std::vector<Token> tokenizeInput(const std::string &line)
    {
        // Separa la entrada en tokens y conserva los lexemas proporcionados
        std::vector<Token> tokens;
        std::istringstream input(line);
        std::string part;
        while (input >> part)
        {
            const auto colon = part.find(':');
            Token token;
            if (colon == std::string::npos)
            {
                token = {part, part};
            }
            else
            {
                token = {part.substr(0, colon), part.substr(colon + 1)};
                if (token.lexeme.empty())
                    token.lexeme = token.kind;
            }
            tokens.push_back(std::move(token));
        }
        return tokens;
    }

    bool validateTokens(const std::vector<Token> &tokens)
    {
        for (std::size_t i = 0; i < tokens.size(); ++i)
        {
            if (!contains(kTerminals, tokens[i].kind))
            {
                std::cout << "Resultado: Cadena invalida\n"
                          << "Motivo: Token desconocido '" << tokens[i].kind
                          << "' en la posicion " << (i + 1) << '\n';
                return false;
            }
            if (tokens[i].kind == "$" && i + 1 != tokens.size())
            {
                std::cout << "Resultado: Cadena invalida\n"
                          << "Motivo: El marcador $ solo puede aparecer al final\n";
                return false;
            }
        }
        return true;
    }

    std::string remainingInput(const std::vector<Token> &tokens, std::size_t from)
    {
        std::string out;
        for (std::size_t i = from; i < tokens.size(); ++i)
        {
            if (!out.empty())
                out += ' ';
            out += tokens[i].kind;
        }
        return out;
    }

    std::string stackText(const std::vector<int> &states,
                          const std::vector<std::string> &symbols)
    {
        // Muestra la pila intercalando estados y simbolos, 0 L 2 = 6
        std::string out = stateLabel(states.front());
        for (std::size_t i = 0; i < symbols.size(); ++i)
            out += " " + symbols[i] + " " + stateLabel(states[i + 1]);
        return out;
    }

    std::string pad(const std::string &text, std::size_t width)
    {
        return text.size() >= width ? text : text + std::string(width - text.size(), ' ');
    }

    void printTrace(const std::vector<TraceRow> &trace)
    {
        const TraceRow header{"Paso", "Pila", "Entrada", "Accion"};
        std::size_t stepWidth = header.step.size();
        std::size_t stackWidth = header.stack.size();
        std::size_t inputWidth = header.input.size();
        for (const auto &row : trace)
        {
            stepWidth = std::max(stepWidth, row.step.size());
            stackWidth = std::max(stackWidth, row.stack.size());
            inputWidth = std::max(inputWidth, row.input.size());
        }

        auto printRow = [&](const TraceRow &row)
        {
            std::cout << pad(row.step, stepWidth + 2) << pad(row.stack, stackWidth + 2)
                      << pad(row.input, inputWidth + 2) << row.action << '\n';
        };
        printRow(header);
        for (const auto &row : trace)
            printRow(row);
    }

    std::unique_ptr<AstNode> makeNode(const std::string &label, const std::string &value)
    {
        auto node = std::make_unique<AstNode>();
        node->label = label;
        node->value = value;
        return node;
    }

    // Accion semantica de cada regla, decide que nodo del AST deja la reduccion
    std::unique_ptr<AstNode> buildAst(int rule, std::vector<std::unique_ptr<AstNode>> &rhs)
    {
        switch (rule)
        {
        case 1: // S -> L = R: La asignacion tiene como hijos el destino y el valor
        {
            auto node = makeNode("Asignacion", "=");
            node->children.push_back(std::move(rhs[0]));
            node->children.push_back(std::move(rhs[2]));
            return node;
        }
        case 3: // L -> * R: Desreferencia del apuntador
        {
            auto node = makeNode("Desreferencia", "*");
            node->children.push_back(std::move(rhs[1]));
            return node;
        }
        case 4: // L -> id: Hoja con el nombre del identificador
            return makeNode("Id", rhs[0]->value);
        default: // S -> R y R -> L solo cambian de categoria, el nodo pasa intacto
            return std::move(rhs[0]);
        }
    }

    void printAst(const AstNode &node, const std::string &prefix, bool isLast, bool isRoot)
    {
        std::cout << prefix;
        if (!isRoot)
            std::cout << (isLast ? "`-- " : "|-- ");
        std::cout << node.label << " (" << node.value << ")\n";

        const std::string childPrefix =
            isRoot ? prefix : prefix + (isLast ? "    " : "|   ");
        for (std::size_t i = 0; i < node.children.size(); ++i)
            printAst(*node.children[i], childPrefix, i + 1 == node.children.size(), false);
    }

    void printSyntaxError(const ActionTable &action, int state, const Token &token,
                          std::size_t tokenIndex)
    {
        std::cout << "Resultado: Cadena invalida\n"
                  << "Estado final: " << stateLabel(state) << '\n'
                  << "Motivo: ACTION[" << stateLabel(state) << "][" << token.kind
                  << "] esta vacia (token " << (tokenIndex + 1) << ": " << token.kind;
        if (token.lexeme != token.kind)
            std::cout << ":" << token.lexeme;
        std::cout << ")\n";

        std::vector<std::string> expected;
        const auto row = action.find(state);
        if (row != action.end())
        {
            for (const auto &terminal : kTerminals)
            {
                if (row->second.count(terminal) != 0)
                    expected.push_back(terminal);
            }
        }

        std::cout << "Se esperaba: ";
        if (expected.empty())
            std::cout << "Ningun token definido en ACTION";
        for (std::size_t i = 0; i < expected.size(); ++i)
            std::cout << (i == 0 ? "" : ", ") << expected[i];
        std::cout << '\n';
    }

    bool parse(const std::vector<Token> &tokens, const Tables &tables)
    {
        // Las tres pilas avanzan juntas, estados, simbolos reconocidos y nodos del AST
        std::vector<int> stateStack{0};
        std::vector<std::string> symbolStack;
        std::vector<std::unique_ptr<AstNode>> nodeStack;
        std::vector<TraceRow> trace;
        std::size_t inputIndex = 0;
        const std::size_t maxSteps = 1000; 

        for (std::size_t step = 1; inputIndex < tokens.size(); ++step)
        {
            if (step > maxSteps)
            {
                printTrace(trace);
                std::cout << "Error interno: Se excedieron " << maxSteps
                          << " pasos\n";
                return false;
            }

            const int state = stateStack.back();
            const Token &lookahead = tokens[inputIndex];
            TraceRow row{std::to_string(step), stackText(stateStack, symbolStack),
                         remainingInput(tokens, inputIndex), ""};

            // Consulta ACTION con el estado actual y el siguiente token
            const auto stateRow = tables.action.find(state);
            if (stateRow == tables.action.end() ||
                stateRow->second.count(lookahead.kind) == 0)
            {
                row.action = "error";
                trace.push_back(row);
                printTrace(trace);
                printSyntaxError(tables.action, state, lookahead, inputIndex);
                return false;
            }

            const Action current = stateRow->second.at(lookahead.kind);
            if (current.kind == ActionKind::Shift)
            {
                // Shift consume el token y apila su simbolo, su hoja y el estado destino
                row.action = actionText(current);
                trace.push_back(row);
                symbolStack.push_back(lookahead.kind);
                nodeStack.push_back(makeNode(lookahead.kind, lookahead.lexeme));
                stateStack.push_back(current.value);
                ++inputIndex;
                continue;
            }

            if (current.kind == ActionKind::Reduce)
            {
                // Reduce saca elementos de cada pila, arma el nodo y sigue GOTO
                const int rule = current.value;
                const Production &production = kProductions.at(static_cast<std::size_t>(rule));
                row.action = actionText(current) + " (" + productionText(rule) + ")";
                trace.push_back(row);

                const std::size_t rhsSize = production.rhs.size();
                if (rhsSize >= stateStack.size() || rhsSize > nodeStack.size())
                {
                    printTrace(trace);
                    std::cout << "Error interno: Pila inconsistente al reducir r"
                              << rule << '\n';
                    return false;
                }

                std::vector<std::unique_ptr<AstNode>> rhs(rhsSize);
                for (std::size_t i = rhsSize; i > 0; --i)
                {
                    rhs[i - 1] = std::move(nodeStack.back());
                    nodeStack.pop_back();
                    symbolStack.pop_back();
                    stateStack.pop_back();
                }

                const int previousState = stateStack.back();
                const auto gotoRow = tables.goTo.find(previousState);
                if (gotoRow == tables.goTo.end() ||
                    gotoRow->second.count(production.lhs) == 0)
                {
                    printTrace(trace);
                    std::cout << "Error en la tabla: Falta GOTO[" << stateLabel(previousState)
                              << "][" << production.lhs << "] despues de r" << rule << '\n';
                    return false;
                }

                symbolStack.push_back(production.lhs);
                nodeStack.push_back(buildAst(rule, rhs));
                stateStack.push_back(gotoRow->second.at(production.lhs));
                continue;
            }

            // Accept, la pila contiene solo S y su nodo es la raiz del AST
            row.action = actionText(current);
            trace.push_back(row);
            printTrace(trace);
            std::cout << "Resultado: Cadena valida\n"
                      << "Estado final: " << stateLabel(state) << " (ACTION["
                      << stateLabel(state) << "][$] = acc)\n"
                      << "AST:\n";
            if (!nodeStack.empty())
                printAst(*nodeStack.back(), "", true, true);
            return true;
        }

        printTrace(trace);
        std::cout << "Resultado: Cadena invalida\n"
                  << "Motivo: Se termino la entrada sin llegar a Accept\n";
        return false;
    }

}

int main()
{
    Tables tables = buildTables();
    validateTables(tables);
    if (!tables.problems.empty())
    {
        std::cout << "La tabla LALR(1) tiene problemas:\n";
        for (const auto &problem : tables.problems)
            std::cout << "  - " << problem << '\n';
        return 1;
    }
    if (tables.action.empty())
    {
        std::cout << "Aviso: La tabla LALR(1) esta vacia.).\n\n";
    }

    std::cout << "Escribe una cadena de tokens por linea (ej: * id:p = id:x).\n"
              << "Termina con Ctrl+D (Linux/Mac) o Ctrl+Z y Enter (Windows).\n";

    std::string line;
    int caseNumber = 0;
    while (std::getline(std::cin, line))
    {
        if (!line.empty() && line.back() == '\r')
            line.pop_back();
        const auto first = line.find_first_not_of(" \t");
        if (first == std::string::npos || line[first] == '#')
            continue;

        std::cout << "\n=== Cadena " << ++caseNumber << ": " << line.substr(first)
                  << " ===\n";
        std::vector<Token> tokens = tokenizeInput(line);
        if (!validateTokens(tokens))
            continue;
        if (tokens.back().kind != "$")
            tokens.push_back({"$", "$"});
        parse(tokens, tables);
    }
    return 0;
}
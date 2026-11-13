
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#define MAX_STATES 100
#define MAX_SYMBOLS 20
#define MAX_STACK 200

typedef struct {
    int to;
    char symbol;
} Transition;

typedef struct {
    Transition trans[MAX_STATES];
    int count;
} State;

State nfa[MAX_STATES];
int nfaStateCount = 0;
int nfaStart, nfaFinal;
char postfix[MAX_STACK];
int postfixLen = 0;
char alphabet[MAX_SYMBOLS];
int alphabetSize = 0;

typedef struct {
    int start;
    int end;
} Fragment;

Fragment stack[MAX_STACK];
int top = -1;

void addTransition(int from, int to, char symbol)
{
    nfa[from].trans[nfa[from].count].to = to;
    nfa[from].trans[nfa[from].count].symbol = symbol;
    nfa[from].count++;
}

int newState()
{
    nfa[nfaStateCount].count = 0;
    return nfaStateCount++;
}

int precedence(char c)
{
    if (c == '*')
        return 3;
    if (c == '.')
        return 2;
    if (c == '|')
        return 1;
    return 0;
}

int isOperand(char c)
{
    return isalnum((unsigned char)c);
}

void addConcatenation(char *regex, char *result)
{
    int i, j = 0;
    int len = strlen(regex);

    for (i = 0; i < len; i++)
    {
        char c1 = regex[i];
        result[j++] = c1;

        if (i + 1 < len)
        {
            char c2 = regex[i + 1];

            if ((isOperand(c1) || c1 == ')' || c1 == '*') &&
                (isOperand(c2) || c2 == '('))
            {
                result[j++] = '.';
            }
        }
    }

    result[j] = '\0';
}

void infixToPostfix(char *regex)
{
    char stackOp[MAX_STACK];
    int topOp = -1;
    postfixLen = 0;

    for (int i = 0; regex[i] != '\0'; i++)
    {
        char c = regex[i];

        if (isOperand(c))
        {
            postfix[postfixLen++] = c;
        }
        else if (c == '(')
        {
            stackOp[++topOp] = c;
        }
        else if (c == ')')
        {
            while (topOp >= 0 && stackOp[topOp] != '(')
            {
                postfix[postfixLen++] = stackOp[topOp--];
            }

            if (topOp >= 0)
                topOp--;
        }
        else
        {
            while (topOp >= 0 &&
                   stackOp[topOp] != '(' &&
                   precedence(stackOp[topOp]) >= precedence(c))
            {
                postfix[postfixLen++] = stackOp[topOp--];
            }

            stackOp[++topOp] = c;
        }
    }

    while (topOp >= 0)
    {
        postfix[postfixLen++] = stackOp[topOp--];
    }

    postfix[postfixLen] = '\0';
}

void buildNFA()
{
    top = -1;
    nfaStateCount = 0;
    alphabetSize = 0;

    for (int i = 0; i < postfixLen; i++)
    {
        char c = postfix[i];

        if (isOperand(c))
        {
            int s = newState();
            int e = newState();

            addTransition(s, e, c);

            Fragment f = {s, e};
            stack[++top] = f;

            int exists = 0;

            for (int j = 0; j < alphabetSize; j++)
            {
                if (alphabet[j] == c)
                    exists = 1;
            }

            if (!exists)
                alphabet[alphabetSize++] = c;
        }
        else if (c == '.')
        {
            Fragment f2 = stack[top--];
            Fragment f1 = stack[top--];

            addTransition(f1.end, f2.start, 'e');

            Fragment f = {f1.start, f2.end};
            stack[++top] = f;
        }
        else if (c == '|')
        {
            Fragment f2 = stack[top--];
            Fragment f1 = stack[top--];

            int s = newState();
            int e = newState();

            addTransition(s, f1.start, 'e');
            addTransition(s, f2.start, 'e');
            addTransition(f1.end, e, 'e');
            addTransition(f2.end, e, 'e');

            Fragment f = {s, e};
            stack[++top] = f;
        }
        else if (c == '*')
        {
            Fragment f1 = stack[top--];

            int s = newState();
            int e = newState();

            addTransition(s, f1.start, 'e');
            addTransition(s, e, 'e');
            addTransition(f1.end, f1.start, 'e');
            addTransition(f1.end, e, 'e');

            Fragment f = {s, e};
            stack[++top] = f;
        }
    }

    nfaStart = stack[top].start;
    nfaFinal = stack[top].end;
}

void printNFA()
{
    printf("\n============================================\n");
    printf("              NFA TRANSITIONS\n");
    printf("============================================\n");

    printf("Start State : q%d\n", nfaStart);
    printf("Final State : q%d\n\n", nfaFinal);

    printf("From\tSymbol\tTo\n");
    printf("------------------------\n");

    for (int i = 0; i < nfaStateCount; i++)
    {
        for (int j = 0; j < nfa[i].count; j++)
        {
            printf("q%d\t", i);

            if (nfa[i].trans[j].symbol == 'e')
                printf("ε\t");
            else
                printf("%c\t", nfa[i].trans[j].symbol);

            printf("q%d\n", nfa[i].trans[j].to);
        }
    }
}

typedef struct {
    int states[MAX_STATES];
    int count;
} StateSet;

StateSet dfaStates[MAX_STATES];
int dfaTransitions[MAX_STATES][MAX_SYMBOLS];
int dfaStateCount = 0;

int contains(StateSet *set, int state)
{
    for (int i = 0; i < set->count; i++)
    {
        if (set->states[i] == state)
            return 1;
    }

    return 0;
}

void epsilonClosure(StateSet *input, StateSet *output)
{
    int stackE[MAX_STATES];
    int topE = -1;

    output->count = 0;

    for (int i = 0; i < input->count; i++)
    {
        output->states[output->count++] = input->states[i];
        stackE[++topE] = input->states[i];
    }

    while (topE >= 0)
    {
        int state = stackE[topE--];

        for (int i = 0; i < nfa[state].count; i++)
        {
            if (nfa[state].trans[i].symbol == 'e')
            {
                int next = nfa[state].trans[i].to;

                if (!contains(output, next))
                {
                    output->states[output->count++] = next;
                    stackE[++topE] = next;
                }
            }
        }
    }
}

void moveState(StateSet *input, char symbol, StateSet *output)
{
    output->count = 0;

    for (int i = 0; i < input->count; i++)
    {
        int state = input->states[i];

        for (int j = 0; j < nfa[state].count; j++)
        {
            if (nfa[state].trans[j].symbol == symbol)
            {
                int next = nfa[state].trans[j].to;

                if (!contains(output, next))
                    output->states[output->count++] = next;
            }
        }
    }
}

int sameSet(StateSet *a, StateSet *b)
{
    if (a->count != b->count)
        return 0;

    for (int i = 0; i < a->count; i++)
    {
        if (!contains(b, a->states[i]))
            return 0;
    }

    return 1;
}

int findDFAState(StateSet *set)
{
    for (int i = 0; i < dfaStateCount; i++)
    {
        if (sameSet(&dfaStates[i], set))
            return i;
    }

    return -1;
}

void printSet(StateSet *set)
{
    printf("{");

    for (int i = 0; i < set->count; i++)
    {
        printf("q%d", set->states[i]);

        if (i < set->count - 1)
            printf(",");
    }

    printf("}");
}

void buildDFA()
{
    dfaStateCount = 0;

    for (int i = 0; i < MAX_STATES; i++)
    {
        for (int j = 0; j < MAX_SYMBOLS; j++)
            dfaTransitions[i][j] = -1;
    }

    StateSet initial;
    initial.count = 1;
    initial.states[0] = nfaStart;

    StateSet closure;
    epsilonClosure(&initial, &closure);

    dfaStates[dfaStateCount++] = closure;

    for (int current = 0; current < dfaStateCount; current++)
    {
        for (int s = 0; s < alphabetSize; s++)
        {
            StateSet moved;
            StateSet closed;

            moveState(&dfaStates[current], alphabet[s], &moved);

            if (moved.count == 0)
            {
                dfaTransitions[current][s] = -1;
                continue;
            }

            epsilonClosure(&moved, &closed);

            int found = findDFAState(&closed);

            if (found == -1)
            {
                found = dfaStateCount;
                dfaStates[dfaStateCount++] = closed;
            }

            dfaTransitions[current][s] = found;
        }
    }
}

void printDFA()
{
    printf("\n============================================\n");
    printf("              DFA TRANSITION TABLE\n");
    printf("============================================\n\n");

    printf("State\t");

    for (int i = 0; i < alphabetSize; i++)
        printf("%c\t", alphabet[i]);

    printf("\n");
    printf("--------------------------------------------\n");

    for (int i = 0; i < dfaStateCount; i++)
    {
        printf("D%d ", i);

        if (i == 0)
            printf("(Start)");

        printf("\t");

        for (int j = 0; j < alphabetSize; j++)
        {
            if (dfaTransitions[i][j] == -1)
                printf("-\t");
            else
                printf("D%d\t", dfaTransitions[i][j]);
        }

        printf("\n");
    }

    printf("\nDFA State Sets:\n");

    for (int i = 0; i < dfaStateCount; i++)
    {
        printf("D%d = ", i);
        printSet(&dfaStates[i]);

        if (contains(&dfaStates[i], nfaFinal))
            printf("  <-- FINAL");

        printf("\n");
    }
}

int simulateDFA(char *input)
{
    int current = 0;

    for (int i = 0; input[i] != '\0'; i++)
    {
        char symbol = input[i];
        int symbolIndex = -1;

        for (int j = 0; j < alphabetSize; j++)
        {
            if (alphabet[j] == symbol)
            {
                symbolIndex = j;
                break;
            }
        }

        if (symbolIndex == -1)
            return 0;

        int next = dfaTransitions[current][symbolIndex];

        if (next == -1)
            return 0;

        current = next;
    }

    return contains(&dfaStates[current], nfaFinal);
}

int main()
{
    char regex[200];

    printf("============================================\n");
    printf(" REGULAR EXPRESSION -> NFA -> DFA SIMULATOR\n");
    printf("============================================\n");

    printf("\nSupported operators:\n");
    printf("  |  = Union\n");
    printf("  *  = Kleene Star\n");
    printf("  ( ) = Parentheses\n");
    printf("  .  = Concatenation (optional)\n");

    printf("\nExample: (a|b)*abb\n");
    printf("\nEnter Regular Expression: ");
    scanf("%199s", regex);

    char regexWithConcat[400];

    addConcatenation(regex, regexWithConcat);

    printf("\nExpression with concatenation: %s\n", regexWithConcat);

    infixToPostfix(regexWithConcat);

    printf("Postfix Expression: %s\n", postfix);

    buildNFA();
    printNFA();

    buildDFA();
    printDFA();

    int number;

    printf("\n============================================\n");
    printf("             TEST DFA STRINGS\n");
    printf("============================================\n");

    printf("\nHow many strings do you want to test? ");
    scanf("%d", &number);

    for (int i = 0; i < number; i++)
    {
        char input[200];

        printf("\nEnter string %d: ", i + 1);
        scanf("%199s", input);

        if (simulateDFA(input))
            printf("Result: ACCEPTED\n");
        else
            printf("Result: REJECTED\n");
    }

    printf("\n============================================\n");
    printf("              SIMULATION COMPLETE\n");
    printf("============================================\n");

    return 0;
}

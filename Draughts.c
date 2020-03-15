#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>
/*
CHESS is the type of the bitboard*/
typedef unsigned int CHESS;
/*
DEBUG=1 means the required chessboard while debugging will be printed.
DEBUG=0 means you are not debugging.*/
#define DEBUG 0
/*
MAXSIZE means the maximum size of the hash list.*/
#define MAXSIZE 2000010
/*
INFINITY means the maximum score you can get in the contest.*/
#define INFINITY 0x3f3f3f3f
/*
MOD is used in hash function.
Some other good mods:
1226959 1635947 2181271 2908361
3877817 5170427 6893911 9 191 891
12255871 16341163 21788233*/
#define MOD 1226959
/*
Make the rules of the chessboard index as follows.*/
#define WHITE 0
#define BLACK 1
#define KING 2
/*
Make the rules of the absolute direction as follows.*/
#define UP 1
#define DOWN 0
#define OUTSIDE 1
#define INSIDE 0
/*
Make the rules of the BFS queue index as follows.*/
#define MINE 0
#define ENEMY 1
#define POSITION 2

/*
Suppose that the chessboard in this program looks like this.
,,,,,,,,,,,,,,,,,,
| 0 x 0 x 0 x 0 x|7
| x 0 x 0 x 0 x 0|6
| 0 x 0 x 0 x 0 x|5
| x 0 x 0 x 0 x 0|4
| 0 x 0 x 0 x 0 x|3
| x 0 x 0 x 0 x 0|2
| 0 x 0 x 0 x 0 x|1
| x 0 x 0 x 0 x 0|0
``````````````````
  7 6 5 4 3 2 1 0
It is a reverse of the real chessboard.
Then delete all the useless position which labels 0.
,,,,,,,,,,
| x x x x|7
| x x x x|6
| x x x x|5
| x x x x|4
| x x x x|3
| x x x x|2
| x x x x|1
| x x x x|0
``````````
  3 2 1 0
In the end,make sure that the chessboard looks like this.
,,,,,,,,,
|xxxx   |7
|xxxx   |6
| xxxx  |5
| xxxx  |4
|  xxxx |3
|  xxxx |2
|   xxxx|1
|   xxxx|0
`````````
    3210
It can be represented with a 32 bit interger.
The bits goes like this:
31...28
27.....
.......
......4
3 2 1 0*/

/*
This function is used to print the whole chessboard*/
void Debug(const CHESS chessboard[])
{
    printf("DEBUG \nDEBUG ****************\nDEBUG ");
    for (int j = 0; j < 8; j++)
    {
        for (int i = 0; i < 4; i++)
        {
            if (!(j & 1))
                printf("0");
            printf("%d", (chessboard[1] & (1 << (CHESS)(4 * (7 - j) + 3 - i))) ? 2 : ((chessboard[0] & (1 << (CHESS)(4 * (7 - j) + 3 - i))) ? 1 : 0));
            if ((j & 1))
                printf("0");
        }
        printf(" %d", 7 - j);
        if (j == 7)
            printf("X");
        printf("\nDEBUG ");
    }
    printf("\nDEBUG ");
    for (int i = 7; i >= 0; i--)
        printf("%d", i);
    printf("\nDEBUG ");
    for (int i = 6; i >= 0; i--)
        printf(" ");
    printf("Y\nDEBUG ****************\nDEBUG\n");
    fflush(stdout);
}

/*
Parameters used to evaluate fuction*/
const int kEvaluateNumber = 15;
const int kEvaluateType = 16;
/*
Constants used to generate moving method*/
const CHESS kCutMove[2][2] = {{0xefefefe0, 0x0fefefef}, {0xf7f7f7f0, 0x07f7f7f7}};
const CHESS kCutJump[2][2] = {{0xeeeeee00, 0x00eeeeee}, {0x77777700, 0x00777777}};
const CHESS kKing[2] = {0xf0000000, 0x0000000f};
const CHESS kEven = 0x0f0f0f0f;
/*
Variables used to control running time*/
long long clock_start;
long long clock_end;
const long long time_limit = 1600;
/*
This array is used to save the output result.*/
CHESS output[150][3];
/*
This variable represents the color of gamer.*/
int my_side;
/*
Ths variable represents whether the time is about to running out.*/
int time_out;
/*
These variables count the number of turns and nodes.*/
int turn;
int node_count;
/*
This variable records the answer of last iteration.*/
int former_value;

typedef struct Methodlist
{
    CHESS chessboard[3];
    int value;
} METHOD;
METHOD method[2019];
int key[2019];
int method_index;

CHESS queue[300][3];
int queue_head = 1;
int queue_tail = 0;

typedef struct Hashlist
{
    CHESS expect[3];
    int value;
    CHESS chessboard[3];
    int next;
} HASH;
HASH hash[MAXSIZE];
int hash_index;
int hash_head[2][MOD];

typedef struct Expect
{
    int size;
    CHESS chessboard[35][3];
} EXPECT;

int Count(CHESS chessboard)
{
    chessboard = ((chessboard >> 1) & 0x55555555) + (chessboard & 0x55555555);
    chessboard = ((chessboard >> 2) & 0x33333333) + (chessboard & 0x33333333);
    chessboard = ((chessboard >> 4) & 0x0f0f0f0f) + (chessboard & 0x0f0f0f0f);
    chessboard = ((chessboard >> 8) & 0x00ff00ff) + (chessboard & 0x00ff00ff);
    return (chessboard >> 16) + (chessboard & 0x0000ffff);
}

CHESS Move(const CHESS position, const int horizontal, const int vertical)
{
    return vertical ? (position << (3 + horizontal + (1 ^ (!(kEven & position)))))
                    : (position >> (3 + (1 ^ horizontal) + (!(kEven & position))));
}

CHESS Jump(const CHESS position, const int horizontal, const int vertical)
{
    return vertical ? (position << (7 + (horizontal << 1)))
                    : (position >> (7 + ((horizontal ^ 1) << 1)));
}

void QueueReset(void)
{
    queue_head = 1;
    queue_tail = 0;
}

void QueuePush(const CHESS state, const CHESS bridge, const CHESS position)
{
    ++queue_tail;
    queue[queue_tail][MINE] = state;
    queue[queue_tail][ENEMY] = bridge;
    queue[queue_tail][POSITION] = position;
}

void QueuePop(CHESS *state, CHESS *bridge, CHESS *position)
{
    (*state) = queue[queue_head][MINE];
    (*bridge) = queue[queue_head][ENEMY];
    (*position) = queue[queue_head][POSITION];
    queue_head++;
}

void OneDirectionJump(const CHESS enemy, const CHESS state, const CHESS bridge,
                      const CHESS position, const int horizontal, const int vertical)
{
    if (!((position & kCutMove[horizontal][vertical]) && (position & kCutJump[horizontal][vertical])))
    {
        return;
    }
    int move = Move(position, horizontal, vertical);
    int jump = Jump(position, horizontal, vertical);
    if ((move & (enemy ^ bridge)) && (jump & (~(state | enemy))))
    {
        QueuePush(state ^ (position | jump), bridge | move, jump);
    }
}

int FindPossibleJump(const CHESS chessboard[], const int side)
{
    int start = method_index;
    CHESS generate = chessboard[side];
    CHESS state = chessboard[side];
    CHESS bridge = 0, position = 0;
    QueueReset();
    while (generate)
    {
        position = generate & ((~generate) + 1);
        QueuePush(state, 0, position);
        generate ^= position;
    }
    while (queue_head <= queue_tail)
    {
        QueuePop(&state, &bridge, &position);
        OneDirectionJump(chessboard[side ^ 1], state, bridge, position, side ^ 1, side ^ 1);
        OneDirectionJump(chessboard[side ^ 1], state, bridge, position, side, side ^ 1);
        OneDirectionJump(chessboard[side ^ 1], state, bridge, position, side ^ 1, side);
        OneDirectionJump(chessboard[side ^ 1], state, bridge, position, side, side);
    }
    if (!queue[queue_tail][ENEMY])
        return 0;
    while (Count(queue[--queue_head][ENEMY]) == Count(queue[queue_tail][ENEMY]))
        ;
    while ((++queue_head) <= queue_tail)
    {
        ++method_index;
        key[method_index] = method_index;
        method[method_index].chessboard[side] = queue[queue_head][MINE];
        method[method_index].chessboard[side ^ 1] = chessboard[side ^ 1] ^ queue[queue_head][ENEMY];
        method[method_index].chessboard[KING] = chessboard[KING] ^ (chessboard[KING] & queue[queue_head][ENEMY]);
        method[method_index].chessboard[KING] = method[method_index].chessboard[KING] & (chessboard[side] ^ queue[queue_head][MINE]) ? method[method_index].chessboard[KING] ^ (chessboard[side] ^ queue[queue_head][MINE]) : method[method_index].chessboard[KING];
        method[method_index].chessboard[KING] |= queue[queue_head][MINE] & kKing[side];
    }
    return method_index - start;
}

void OneDirectionMove(const CHESS chessboard[], const CHESS position,
                      const int side, const int horizontal, const int vertical)
{
    if (!(position & kCutMove[horizontal][vertical]))
    {
        return;
    }
    CHESS move = Move(position, horizontal, vertical);
    if (!(move & (~(chessboard[side] | chessboard[side ^ 1]))))
        return;
    method_index++;
    move ^= position;
    key[method_index] = method_index;
    method[method_index].chessboard[side] = chessboard[side] ^ move;
    method[method_index].chessboard[side ^ 1] = chessboard[side ^ 1];
    method[method_index].chessboard[KING] = (chessboard[KING] & position) ? chessboard[KING] ^ move : chessboard[KING];
    method[method_index].chessboard[KING] |= method[method_index].chessboard[side] & kKing[side];
}

int FindPossibleMove(const CHESS chessboard[], const int side)
{
    int start = method_index;
    CHESS generate = chessboard[side];
    while (generate)
    {
        CHESS position = generate & ((~generate) + 1);
        OneDirectionMove(chessboard, position, side, side ^ 1, side ^ 1);
        OneDirectionMove(chessboard, position, side, side, side ^ 1);
        generate ^= position;
    }
    generate = chessboard[side] & chessboard[KING];
    while (generate)
    {
        CHESS position = generate & ((~generate) + 1);
        OneDirectionMove(chessboard, position, side, side ^ 1, side);
        OneDirectionMove(chessboard, position, side, side, side);
        generate ^= position;
    }
    return method_index - start;
}

int ChessToCoordinate(const CHESS state)
{
    int temp = 0;
    while (!(state & (1 << temp)))
        temp++;
    return (temp << 1) + !(((temp >> 2) & 1));
}

CHESS CoordinateToChess(const int x, const int y)
{
    return (1 << ((y << 2) | (x >> 1)));
}

void OneDirectionOutput(CHESS *position, CHESS *bridge, const int horizontal, const int vertical)
{
    if (!(((*position) & kCutMove[horizontal][vertical]) && ((*position) & kCutJump[horizontal][vertical])))
    {
        return;
    }
    if (Move(*position, horizontal, vertical) & (*bridge))
    {
        (*bridge) ^= Move(*position, horizontal, vertical);
        (*position) = Jump(*position, horizontal, vertical);
        int end = ChessToCoordinate(*position);
        printf(" %d,%d", end >> 3, end & 7);
        fflush(stdout);
    }
    return;
}

void Output(const CHESS chessboard[], int side)
{
    int cnt = 2;
    CHESS temp = chessboard[side] ^ output[turn][side];
    CHESS bridge = chessboard[side ^ 1] ^ output[turn][side ^ 1];
    int start = ChessToCoordinate(chessboard[side] & temp);
    int end = ChessToCoordinate(output[turn][side] & temp);
    if (bridge)
    {
        printf("%d %d,%d", Count(bridge) + 1, start >> 3, start & 7);
        fflush(stdout);
        CHESS position = chessboard[side] & temp;
        while (bridge)
        {
            OneDirectionOutput(&position, &bridge, 1, 0);
            OneDirectionOutput(&position, &bridge, 1, 1);
            OneDirectionOutput(&position, &bridge, 0, 1);
            OneDirectionOutput(&position, &bridge, 0, 0);
        }
        printf("\n");
        fflush(stdout);
    }
    else
    {
        printf("%d %d,%d %d,%d\n", cnt, start >> 3, start & 7, end >> 3, end & 7);
        fflush(stdout);
    }
    return;
}

void Input(CHESS chessboard[])
{
    int number;
    scanf("%d", &number);
    int y[40], x[40];
    for (int i = 1; i <= number; i++)
    {
        scanf("%d,%d", &y[i], &x[i]);
    }
    CHESS start = CoordinateToChess(x[1], y[1]);
    CHESS end = CoordinateToChess(x[number], y[number]);
    chessboard[my_side ^ 1] ^= start | end;
    chessboard[KING] = start & chessboard[KING] ? (chessboard[KING] ^ (start | end)) : chessboard[KING];
    chessboard[KING] |= end & kKing[my_side ^ 1];
    if ((x[1] - x[2]) * (x[1] - x[2]) * (y[1] - y[2]) * (y[1] - y[2]) != 1)
    {
        for (int i = 2; i <= number; i++)
        {
            int col = (y[i] + y[i - 1]) >> 1;
            int row = (x[i] + x[i - 1]) >> 1;
            chessboard[my_side] ^= CoordinateToChess(row, col);
            chessboard[KING] ^= chessboard[KING] & CoordinateToChess(row, col);
        }
    }
    output[turn][WHITE] = chessboard[WHITE];
    output[turn][BLACK] = chessboard[BLACK];
    output[turn][KING] = chessboard[KING];
}

int Evaluate(const CHESS chessboard[], const int side)
{
    int value = 0;
    value += Count(chessboard[side]) << kEvaluateNumber;
    value += Count(chessboard[side] & chessboard[KING]) << kEvaluateType;
    return value;
}

void MethodSort(const int start, const int end)
{
    int i = start;
    int j = end;
    int mid = method[key[(start + end) >> 1]].value;
    while (i <= j)
    {
        while (method[key[i]].value > mid)
            i++;
        while (method[key[j]].value < mid)
            j--;
        if (i <= j)
        {
            int temp = key[i];
            key[i] = key[j];
            key[j] = temp;
            i++;
            j--;
        }
    }
    if (start < j)
        MethodSort(start, j);
    if (i < end)
        MethodSort(i, end);
    return;
}

int Hash(const CHESS chessboard[])
{
    return ((chessboard[WHITE] >> 3) ^ chessboard[KING] ^ (chessboard[BLACK] << 3)) % MOD;
}

int HashFind(const CHESS chessboard[], int side)
{
    int pos = Hash(chessboard);
    for (int i = hash_head[side][pos]; i; i = hash[i].next)
    {
        HASH *node = &hash[i];
        if (node->chessboard[WHITE] == chessboard[WHITE] && node->chessboard[BLACK] == chessboard[BLACK] && node->chessboard[KING] == chessboard[KING])
        {
            return i;
        }
    }
    return 0;
}

int HashPush(const CHESS chessboard[], const CHESS expect[], const int side)
{
    int pos = Hash(chessboard);
    ++hash_index;
    HASH *node = &hash[hash_index];
    node->chessboard[WHITE] = chessboard[WHITE];
    node->chessboard[BLACK] = chessboard[BLACK];
    node->chessboard[KING] = chessboard[KING];
    node->expect[WHITE] = expect[WHITE];
    node->expect[BLACK] = expect[BLACK];
    node->expect[KING] = expect[KING];
    node->next = hash_head[side][pos];
    hash_head[side][pos] = hash_index;
    return hash_index;
}

void CopyChessboard(CHESS to[], CHESS from[])
{
    to[WHITE] = from[WHITE];
    to[BLACK] = from[BLACK];
    to[KING] = from[KING];
}

int AlphaBeta(const int level, const int depth, int alpha, int beta,
              const CHESS chessboard[], const int side, EXPECT *father)
{
    father->size = 0;
    if (!chessboard[side])
        return -INFINITY;
    if (!chessboard[side ^ 1])
        return INFINITY;
    if (turn + depth >= 120)
        return (Count(chessboard[side]) - Count(chessboard[side ^ 1]) + ((Count(chessboard[side] & chessboard[KING]) - Count(chessboard[side ^ 1] & chessboard[KING])) << 1)) > 0 ? INFINITY : -INFINITY;
    node_count++;
    EXPECT expect;
    int pvs = 0;
    int start = method_index + 1;
    int end = start;
    int pos = HashFind(chessboard, side);
    HASH *node = &hash[pos];
    int flag = FindPossibleJump(chessboard, side);
    if (!flag)
    {
        if (depth >= level)
        {
            return Evaluate(chessboard, side) - Evaluate(chessboard, side ^ 1);
        }
        flag = FindPossibleMove(chessboard, side);
    }
    if (flag)
    {
        end = method_index;
        /*for (int i = start; i <= end; i++)
            method[i].value = Evaluate(method[i].chessboard, side) - Evaluate(method[i].chessboard, side ^ 1);
        MethodSort(start, end);*/
    }
    else
        return -INFINITY;
    if (pos)
    {
        int value = -AlphaBeta(level, depth + 1, -beta, -alpha, node->expect, side ^ 1, &expect);
        if (value >= beta)
        {
            method_index = start - 1;
            return beta;
        }
        if (value > alpha)
        {
            pvs = 1;
            alpha = value;
            father->size = expect.size + 1;
            CopyChessboard(father->chessboard[0], node->expect);
            for (int i = 0; i < expect.size; i++)
                CopyChessboard(father->chessboard[i + 1], expect.chessboard[i]);
            if (!depth && former_value <= alpha)
                CopyChessboard(output[turn], node->expect);
        }
        clock_end = clock();
        if ((long long)clock_end - (long long)clock_start >= (long long)time_limit)
        {
            time_out = 1;
            method_index = start - 1;
            return alpha;
        }
    }
    for (int i = start; i <= end; i++) /*search all the method*/
    {
        int temp = key[i];
        if (temp && method[temp].chessboard[WHITE] == node->expect[WHITE] && method[temp].chessboard[BLACK] == node->expect[BLACK] && method[temp].chessboard[KING] == node->expect[KING])
            continue;
        int value;
        if (pvs)
        {
            value = -AlphaBeta(level, depth + 1, -alpha - 1, -alpha, method[temp].chessboard, side ^ 1, &expect);
            if (value > alpha && value < beta)
                value = -AlphaBeta(level, depth + 1, -beta, -alpha, method[temp].chessboard, side ^ 1, &expect);
        }
        else
            value = -AlphaBeta(level, depth + 1, -beta, -alpha, method[temp].chessboard, side ^ 1, &expect);
        method[temp].value = value;
        if (value >= beta)
        {
            method_index = start - 1;
            return beta;
        }
        if (value > alpha)
        {
            pvs = 1;
            alpha = value;
            father->size = expect.size + 1;
            CopyChessboard(father->chessboard[0], method[temp].chessboard);
            for (int j = 0; j < expect.size; j++)
                CopyChessboard(father->chessboard[j + 1], expect.chessboard[j]);
            if (!depth && former_value <= alpha)
                CopyChessboard(output[turn], method[temp].chessboard);
        }
        clock_end = clock();
        if ((long long)clock_end - (long long)clock_start >= (long long)time_limit)
        {
            time_out = 1;
            method_index = start - 1;
            return alpha;
        }
    }
    method_index = start - 1;
    return alpha;
}

void Search(CHESS chessboard[], const int side)
{
    time_out = 0;
    former_value = -INFINITY - 1;
    int depth;
    for (depth = 1; (turn + depth <= 120) && !time_out && depth <= 15; depth++)
    {
        node_count = 0;
        EXPECT expect;
        former_value = AlphaBeta(depth, 0, -INFINITY - 1, INFINITY + 1, chessboard, side, &expect);
        if (former_value == INFINITY)
            break;
        if (DEBUG)
            printf("DEBUG level:%d expect:%d node:%d value:%d\n", depth, expect.size, node_count, former_value);
        for (int i = 0, chess_side = side; i < expect.size; i++, chess_side ^= 1)
        {
            int rank;
            if (i)
                rank = HashFind(expect.chessboard[i], chess_side);
            else
                rank = HashFind(chessboard, chess_side);
            if (!rank)
            {
                if (i)
                    rank = HashPush(expect.chessboard[i - 1], expect.chessboard[i], chess_side);
                else
                    rank = HashPush(chessboard, expect.chessboard[i], chess_side);
            }
            else
                CopyChessboard(hash[rank].expect, expect.chessboard[i]);
        }
    }
    if (turn >= 30 && output[turn][WHITE] == output[turn - 4][WHITE] && output[turn][BLACK] == output[turn - 4][BLACK] && output[turn][KING] == output[turn - 4][KING] && (Evaluate(output[turn], side) - Evaluate(output[turn], side ^ 1)) < 0)
    {
        int start = method_index;
        if (FindPossibleMove(chessboard, side))
        {
            int pos = start + 1 + rand() % (method_index - start);
            CopyChessboard(output[turn], method[pos].chessboard);
        }
        method_index = start;
    }
    Output(chessboard, side);
    CopyChessboard(chessboard, output[turn]);
    return;
}

void Work(void)
{
    CHESS chessboard[3] = {0x00000fff, 0xfff00000, 0};
    printf("OK\n");
    fflush(stdout);
    char order[10];
    while (1)
    {
        scanf("%s", order);
        clock_start = clock();
        if (order[0] == 'T')
        {
            Search(chessboard, my_side);
            turn++;
            clock_end = clock();
            if (DEBUG)
            {
                Debug(chessboard);
                printf("DEBUG time:%lld\n", clock_end - clock_start);
                fflush(stdout);
                printf("DEBUG hashlist:%d\n", hash_index);
                fflush(stdout);
            }
            continue;
        }
        if (order[0] == 'P')
        {
            Input(chessboard);
            turn++;
            if (DEBUG)
            {
                Debug(chessboard);
            }
            continue;
        }
        if (order[0] == 'E')
        {
            int whatever;
            scanf("%d", &whatever);
            return;
        }
    }
    return;
}

int main(void)
{
    scanf("START %d", &my_side);
    if (my_side == 2)
        my_side = 0;
    Work();
    return 0;
}
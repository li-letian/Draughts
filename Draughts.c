#include<stdio.h>
#include<string.h>
#include<time.h>
#define DEBUG 0
/***********PART 0 DEFINATION*********/
/*about the size*/
#define MAXSIZE 9000010
/*each turn contributes to 1 200 000 moehod and 280 000 node*/
/*each turn makes about 17 depth search*/
/*that is for about 1500 seconds*/
/*so the right size should at least be 90 000 000*/
/*but 350MB memory support at most 20 000 000 large*/
#define INFINITY 0x3f3f3f3f
/*some good mods
1226959 1635947 2181271 2908361
3877817 5170427 6893911 9 191 891
12255871 16341163 21788233*/
#define MOD 1226959
/*about the chess type*/
#define WHITE 0
#define BLACK 1
#define KING 2
/*about the absolote direction*/
#define UP 1
#define DOWN 0
#define OUTSIDE 1
#define INSIDE 0
/*about queue*/
#define MINE 0
#define ENEMY 1
#define POSITION 2
typedef unsigned int CHESS;
/*
suppose my chessboard looks like this
it is just a reverse of the required key board
						7
						6
						5
						4
						3
						2
						1
						0
7 6 5 4 3 2 1 0
but acutally it looks more like
			7
			6
			5
			4
			3
			2
			1
			0
3 2 1 0
and finally it looks like
xxxx       7
xxxx       6
0xxxx     5
0xxxx     4
00xxxx   3
00xxxx   2
000xxxx 1
000xxxx 0
	 3210
and the white chess is beneath the black chess
(so this is just a reversed and simplified board of the required chessboard
and we can still calculate the right position
and my chessboard looks like a unsigned integer
and the bit goes like
31.....28
.............
...........4
3 2 1 0
*/
/*****************PART 0.5 DEBUG************/
inline void debug(const CHESS chessboard[])
{
	printf("\n****************\n");
	fflush(stdout);
	for (int j = 0; j < 8; j++)
	{
		for (int i = 0; i < 4; i++)
		{
			if (!(j & 1))
			{
				printf("0");
				fflush(stdout);
			}
			printf("%d", (chessboard[1] & (1 << (CHESS)(4 * (7 - j) + 3 - i))) ? 2 :
				((chessboard[0] & (1 << (CHESS)(4 * (7 - j) + 3 - i))) ? 1 : 0));
			fflush(stdout);
			if ((j & 1))
			{
				printf("0");
				fflush(stdout);
			}
		}
		printf(" %d", 7 - j);
		fflush(stdout);
		if (j == 7) printf("X");
		fflush(stdout);
		printf("\n");
		fflush(stdout);
	}
	printf("\n");
	fflush(stdout);
	for (int i = 7; i >= 0; i--)
	{
		printf("%d", i);
		fflush(stdout);
	}
	printf("\n");
	fflush(stdout);
	for (int i = 6; i >= 0; i--)
	{
		printf(" ");
		fflush(stdout);
	}
	printf("Y");
	fflush(stdout);
	printf("\n****************\n");
	fflush(stdout);
	printf("\n");
	fflush(stdout);
}
/**********PART 1 PREWORK*************/
/*constant*/
const int kEvaluateNumber = 15;
const int kEvaluateCorner = 4;
const int kEvaluatePosition[2][8] = { {0,0,1,2,3,6,7,8},{8,7,6,3,2,1,0,0} };
const int kEvaluateType = 16;
const long long time_limit = 1700;
const CHESS kCutMove[2][2] = { {0xefefefe0,0x0fefefef},{0xf7f7f7f0,0x07f7f7f7} };
const CHESS kCutJump[2][2] = { {0xeeeeee00,0x00eeeeee}, {0x77777700,0x00777777} };
const CHESS kKing[2] = { 0xf0000000,0x0000000f };
const CHESS kRow[8] = { 0x0000000f,0x000000f0,0x00000f00,0x0000f000,0x000f0000,0x00f00000,0x0f000000,0xf0000000 };
const CHESS kEven = 0x0f0f0f0f;
const CHESS kEdge = 0x09999990;
/*generate a specific direction bitboard move or jump
suppose
the value of horizontal:0 means step right, 1 means step left
the value of vertical:0 means step back, 1 means step forward
chessboard[0]means white
chessboard[1]means black
chessboard[2]means king
*/
/*return the next position */
inline CHESS Move(const CHESS position, const int horizontal, const int vertical)
{
	return vertical ?
		(position << (3 + horizontal + (1 ^ (!(kEven&position))))) :
		(position >> (3 + (1 ^ horizontal) + (!(kEven&position))));
}
/*return the next position of the next position*/
inline CHESS Jump(const CHESS position, const  int horizontal, const int vertical)
{
	return vertical ?
		(position << (7 + (horizontal << 1))) :
		(position >> (7 + ((horizontal ^ 1) << 1)));
}
/*to count how many 1 in its  binary number*/
inline int Count( CHESS chessboard) {
	chessboard = ((chessboard >> 1) & 0x55555555) + (chessboard & 0x55555555);
	chessboard = ((chessboard >> 2) & 0x33333333) + (chessboard & 0x33333333);
	chessboard = ((chessboard >> 4) & 0x0f0f0f0f) + (chessboard & 0x0f0f0f0f);
	chessboard = ((chessboard >> 8) & 0x00ff00ff) + (chessboard & 0x00ff00ff);
	return (chessboard >> 16) + (chessboard & 0x0000ffff);
}
/*********PART 2 FIND WAYS TO GO**********/
/*the list to save the moving method and its index
for each side and chessboard statement
we generate a list including every possible single move or every possible jump
and return its size*/
typedef struct Methodlist
{
	CHESS chessboard[3];
	int value;
}METHOD;
METHOD method[MAXSIZE];
int key[MAXSIZE];
int method_index;
/*the queue to bfs and its head and tail
queue[i][0]saves chessboard of present statement of all my chess
queue[i][1]saves chessboard of beaten enemy
queue[i][2]saves chessboard of present extending position*/
CHESS queue[300][3];
int queue_head = 1, queue_tail = 0;
inline void QueueReset(void)
{
	queue_head = 1;
	queue_tail = 0;
}
inline void QueuePush(const CHESS state, const CHESS bridge, const CHESS position)
{
	++queue_tail;
	queue[queue_tail][MINE] = state;
	queue[queue_tail][ENEMY] = bridge;
	queue[queue_tail][POSITION] = position;
}
inline void QueuePop(CHESS *state, CHESS *bridge, CHESS *position)
{
	(*state) = queue[queue_head][MINE];
	(*bridge) = queue[queue_head][ENEMY];
	(*position) = queue[queue_head][POSITION];
	queue_head++;
}
inline void OneDirectionJump(const CHESS enemy, const CHESS state, const CHESS bridge, const CHESS position, const int horizontal, const int vertical)
{
	if (!((position&kCutMove[horizontal][vertical]) && (position&kCutJump[horizontal][vertical])))
	{
		return;
	}
	int move = Move(position, horizontal, vertical);
	int jump = Jump(position, horizontal, vertical);
	if ((move&(enemy^bridge)) && (jump&(~(state | enemy))))
	{
		QueuePush(state ^ (position | jump), bridge | move, jump);
	}
}
inline int  FindPossibleJump(const CHESS chessboard[], const int side)
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
	if (!queue[queue_tail][ENEMY]) return 0;
	while (Count(queue[--queue_head][ENEMY]) == Count(queue[queue_tail][ENEMY]));
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
inline void OneDirectionMove(const CHESS chessboard[], const CHESS position, const int side, const int horizontal, const int vertical)
{
	if (!(position&kCutMove[horizontal][vertical]))
	{
		return;
	}
	CHESS move = Move(position, horizontal, vertical);
	if (!(move&(~(chessboard[side] | chessboard[side ^ 1])))) return;
	method_index++;
	move ^= position;
	key[method_index] = method_index;
	method[method_index].chessboard[side] = chessboard[side] ^ move;
	method[method_index].chessboard[side ^ 1] = chessboard[side ^ 1];
	method[method_index].chessboard[KING] = (chessboard[KING] & position) ? chessboard[KING] ^ move : chessboard[KING];
	method[method_index].chessboard[KING] |= method[method_index].chessboard[side] & kKing[side];
}/*debug finished*/
inline int FindPossibleMove(const CHESS chessboard[], const int side)
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
}/*debug finidhed*/
/**********PART 3 INPUT AND OUTPUT**********/
CHESS output[3];
int my_side;
int time_out;
int memory_out;
int turn;
inline int ChessToCoordinate(const CHESS state)
{
	int temp = 0;
	while (!(state&(1 << temp))) temp++;
	return (temp << 1) + !(((temp >> 2) & 1));
}
inline CHESS CoordinateToChess(const int x, const int y)
{
	return (1 << ((y << 2) | (x >> 1)));
}
inline void OneDirectionOutput(CHESS * position, CHESS *bridge, const int horizontal, const int vertical)
{
	if (!(((*position)&kCutMove[horizontal][vertical]) && ((*position)&kCutJump[horizontal][vertical])))
	{
		return;
	}
	if (Move(*position, horizontal, vertical)&(*bridge))
	{
		(*bridge) ^= Move(*position, horizontal, vertical);
		(*position) = Jump(*position, horizontal, vertical);
		int end = ChessToCoordinate(*position);
		printf(" %d,%d", end >> 3, end & 7);
		fflush(stdout);
	}
	return;
}
inline void Output( const CHESS chessboard[], int side)
{
	int cnt = 2;
	CHESS temp = chessboard[side] ^ output[side];
	CHESS bridge = chessboard[side ^ 1] ^ output[side ^ 1];
	int start = ChessToCoordinate(chessboard[side] & temp);
	int end = ChessToCoordinate(output[side] & temp);
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
inline void Input(CHESS chessboard[])
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
	if ((x[1] - x[2])*(x[1] - x[2])*(y[1] - y[2])*(y[1] - y[2]) != 1)
	{
		for (int i = 2; i <= number; i++)
		{
			int col = (y[i] + y[i - 1]) >> 1;
			int row = (x[i] + x[i - 1]) >> 1;
			chessboard[my_side] ^= CoordinateToChess(row, col);
			chessboard[KING] ^= chessboard[KING] & CoordinateToChess(row, col);
		}
	}
}

/**********************PART 4 SEARCH******************/
inline int Evaluate( const CHESS chessboard[], const int side)
{
	int value = 0;
	int mine = Count(chessboard[side]);
	int enemy = Count(chessboard[side ^ 1]);
	int number = mine < enemy ? mine : enemy;
	if (number >= 10)
	{
		value += mine << kEvaluateNumber;
		value += Count(chessboard[side] & kEdge) << kEvaluateCorner;
		value += Count(chessboard[side] & chessboard[KING]) << kEvaluateType;
	}
	else if (number >= 5)
	{
		value += mine << kEvaluateNumber;
		value += Count(chessboard[side] & chessboard[KING]) << kEvaluateType;
		for (int i = 0; i < 8; i++)
		{
			value += Count(chessboard[side] & kRow[i]) << kEvaluatePosition[side][i];
		}
	}
	else
	{
		value += mine << kEvaluateNumber;
		value += (Count(chessboard[side] & chessboard[KING])) << (kEvaluateType + 2);
	}
	return value;
}

/*key saves the index of a rank in one node*/
void MethodSort(const int start, const int end)
{
	int i = start;
	int j = end;
	int mid = method[key[(start + end) / 2]].value;
	while (i <= j)
	{
		while (method[key[i]].value > mid) i++;
		while (method[key[j]].value < mid) j--;
		if (i <= j)
		{
			int temp = key[i];
			key[i] = key[j];
			key[j] = temp;
			i++; j--;
		}
	}
	if (start < j)  MethodSort(start, j);
	if (i < end)  MethodSort(i, end);
	return;
}

/*hash the chessboard to find its interval of key*/
typedef struct Hashlist
{
	int start;
	int end;
	CHESS expect[3];
	CHESS chessboard[3];
	int next;
}HASH;
HASH hash[MAXSIZE/4];
int hash_index;
int hash_head[2][MOD];

inline int Hash(const CHESS chessboard[])
{
	return ((chessboard[WHITE] >> 3) ^ chessboard[KING] ^ (chessboard[BLACK] << 3)) % MOD;
}
inline int HashFind(const CHESS chessboard[], int side)
{
	int pos = Hash(chessboard);
	for (int i = hash_head[side][pos]; i; i = hash[i].next)
	{
		HASH *node = &hash[i];
		if (node->chessboard[WHITE] == chessboard[WHITE]
			&& node->chessboard[BLACK] == chessboard[BLACK]
			&& node->chessboard[KING] == chessboard[KING])
		{
			return i;
		}
	}
	return 0;
}
inline int HashPush(const CHESS chessboard[], const int start, const int end, const int side)
{
	int pos = Hash(chessboard);
	++hash_index;
	HASH *node = &hash[hash_index];
	node->start = start;
	node->end = end;
	node->chessboard[WHITE] = chessboard[WHITE];
	node->chessboard[BLACK] = chessboard[BLACK];
	node->chessboard[KING] = chessboard[KING];
	node->next = hash_head[side][pos];
	hash_head[side][pos] = hash_index;
	return hash_index;
}
long long clock_start;
long long clock_end;
typedef struct Expect
{
	int size;
	CHESS chessboard[35][3];
}EXPECT;
int AlphaBeta(const int level, const int depth, int alpha, int beta, const CHESS chessboard[], const int side, EXPECT *father)
{
	father->size = 0;
	if (!chessboard[side]) return -INFINITY;
	if (!chessboard[side ^ 1]) return INFINITY;
	if (turn + depth >= 120) 
		return (Count(chessboard[side]) - Count(chessboard[side ^ 1]) 
			+ ((Count(chessboard[side] & chessboard[KING]) 
			- Count(chessboard[side ^ 1] & chessboard[KING])) << 1))
			>0? INFINITY:-INFINITY;
	if (depth == level)
	{
		return Evaluate(chessboard, side) - Evaluate(chessboard, side ^ 1);
	}
	EXPECT expect;
	int pvs = 0;
	int start = method_index+1;
	int end = start;
	int rank = HashFind(chessboard, side);
	HASH *node = &hash[rank];
	if (!rank)/*the methods haven't been generated before*/
	{
		if (FindPossibleJump(chessboard, side) || FindPossibleMove(chessboard, side))
		{
			end = method_index;
			for (int i = start ; i <= end; i++)
			{
				method[i].value = Evaluate(method[i].chessboard, side) - Evaluate(method[i].chessboard, side ^ 1);
			}
			MethodSort(start , end);
			if (method_index > (MAXSIZE / 125)*(1 + turn))
			{
				memory_out = 1;
			}
		}
		else/*nowhere to go you have lost*/
		{
			return -INFINITY;
		}
	}
	else
	{
		start = (node->start);
		end = (node->end);
		if (node->expect[side])/*if exists,search the expected method*/
		{
			int value = -AlphaBeta(level, depth + 1, -beta, -alpha, node->expect, side ^ 1, &expect);
			if (value >= beta)
			{
				return beta;
			}
			if (value > alpha)
			{
				pvs = 1;
				alpha = value;
				father->size = expect.size + 1;
				father->chessboard[0][WHITE] = node->expect[WHITE];
				father->chessboard[0][BLACK] = node->expect[BLACK];
				father->chessboard[0][KING] = node->expect[KING];
				for (int i = 0; i < expect.size; i++)
				{
					father->chessboard[i + 1][WHITE] = expect.chessboard[i][WHITE];
					father->chessboard[i + 1][BLACK] = expect.chessboard[i][BLACK];
					father->chessboard[i + 1][KING] = expect.chessboard[i][KING];
				}
				if (!depth)
				{
					output[WHITE] = node->expect[WHITE];
					output[BLACK] = node->expect[BLACK];
					output[KING] = node->expect[KING];
				}
			}
			clock_end = clock();
			if ((long long)clock_end - (long long)clock_start >= (long long)time_limit)
			{
				time_out = 1;
				return alpha;
			}
		}
	}
	for (int i = start ; i <= end; i++)/*search all the method*/
	{
		int pos = key[i];
		if (rank&&method[pos].chessboard[WHITE] == node->expect[WHITE]
			&& method[pos].chessboard[BLACK] == node->expect[BLACK]
			&& method[pos].chessboard[KING] == node->expect[KING])
			continue;
		int value;
		if (pvs)/*have a try if this node is a pvs*/
		{
			value = -AlphaBeta(level, depth + 1, -alpha - 1, -alpha, method[pos].chessboard, side ^ 1, &expect);
			if (value > alpha&&value < beta)
			{
				value = -AlphaBeta(level, depth + 1, -beta, -alpha, method[pos].chessboard, side ^ 1, &expect);
			}
		}
		else
		{
			value = -AlphaBeta(level, depth + 1, -beta, -alpha, method[pos].chessboard, side ^ 1, &expect);
		}
		method[pos].value = value;
		if (value >= beta)
		{
			if (!rank)
			{
				if (!memory_out)
				{
					MethodSort(start, i);
					rank = HashPush(chessboard, start , end, side);
				}
				else
				{
					method_index = start - 1;
				}
			}
			else
			{
				MethodSort(start, i);
			}
			return beta;
		}
		if (value > alpha)
		{
			pvs = 1;
			alpha = value;
			father->size = expect.size + 1;
			father->chessboard[0][WHITE]=method[pos].chessboard[WHITE];
			father->chessboard[0][BLACK] = method[pos].chessboard[BLACK];
			father->chessboard[0][KING] = method[pos].chessboard[KING];
			for (int j = 0; j < expect.size; j++)
			{
				father->chessboard[j+1][WHITE] = expect.chessboard[j][WHITE];
				father->chessboard[j+1][BLACK] = expect.chessboard[j][BLACK];
				father->chessboard[j+1][KING] = expect.chessboard[j][KING];
			}
			if (!depth)
			{
				output[WHITE] = method[pos].chessboard[WHITE];
				output[BLACK] = method[pos].chessboard[BLACK];
				output[KING] = method[pos].chessboard[KING];
			}
		}
		clock_end = clock();
		if ((long long)clock_end - (long long)clock_start >= (long long)time_limit)
		{
			time_out = 1;
			if (!rank)
			{
				if (!memory_out)
				{
					MethodSort(start, i);
					rank = HashPush(chessboard, start, end, side);
				}
				else
				{
					method_index = start - 1;
				}
			}
			else
			{
				MethodSort(start, i);
			}
			return alpha;
		}
	}
	if (!rank)
	{
		if (!memory_out)
		{
			MethodSort(start, end);
			rank = HashPush(chessboard, start, end, side);
		}
		else
		{
			method_index = start - 1;
		}
	}
	else
	{
		MethodSort(start, end);
	}
	return alpha;
}

/**********PART 5 WORK**************/
void Search(CHESS chessboard[], const int side)
{
	time_out = 0;
	memory_out = 0;
	int depth;
	/*about five steps the list should be reset*/
	for (depth = 1; (turn + depth <= 120) && !time_out; depth += 2)
	{
		EXPECT expect;
		if (INFINITY == AlphaBeta(depth, 0, -INFINITY, INFINITY, chessboard, side, &expect))
		{
			break;
		}
		if (DEBUG)
		{
			printf("level:%d expect:%d\n", depth, expect.size);
		}
		for (int i = 0, chess_side = side; i < expect.size; i++,chess_side^=1)
		{
			/*if its hash do not exist,push hash and its expect and method and sort it out*/
			int rank = HashFind(expect.chessboard[i], chess_side);
			if (!rank)
			{
				int start = method_index+1;
				if (FindPossibleJump(expect.chessboard[i], chess_side) || FindPossibleMove(expect.chessboard[i], chess_side))
				{
					rank = HashPush(expect.chessboard[i], start ,method_index,chess_side);
					MethodSort(start , method_index);
				}
			}
		}
	}
	Output(chessboard, side);
	chessboard[WHITE] = output[WHITE];
	chessboard[BLACK] = output[BLACK];
	chessboard[KING] = output[KING];
	return;
}
void Work(void)
{
	CHESS chessboard[3] = { 0x00000fff,0xfff00000,0 };
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
				debug(chessboard);
				printf("time:%lld\n", clock_end - clock_start);
				fflush(stdout);
				printf("methodlist:%d\n", method_index);
				fflush(stdout);
				printf("hashlist:%d\n", hash_index);
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
				debug(chessboard);
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
int main()
{
	scanf("START %d", &my_side);
	if (my_side == 2) my_side = 0;
	Work();
	return 0;
}
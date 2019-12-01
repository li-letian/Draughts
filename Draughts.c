#include<stdio.h>
//#include<string.h>
//#include<time.h>
//#include<windows.h>
typedef unsigned int CHESS;
#define MAXLS 10000010
#define INFINITY 0x3f3f3f3f
#define MOD 1226959
#define MAXHS 11
#define DEBUG print();
/*about the type*/
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
/*
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
/**********PART 1 PREWORK*************/
/*constant*/

const CHESS kCutMove[2][2] = { {0xefefefe0,0x0fefefef},{0xf7f7f7f0,0x07f7f7f7} };
const CHESS kCutJump[2][2] = { {0xeeeeee00,0x00eeeeee}, {0x77777700,0x00777777} };
const CHESS kKing = 0xf000000f;
const CHESS kEven = 0x0f0f0f0f;
const CHESS kChessBoard = 0xffffffff;
/*generate a specific direction bitboard move or jump*/
/*
suppose
the value of horizontal:0 means step right, 1 means step left
the value of vertical:0 means step back, 1 means step forward
chessboard[0]means white 
chessboard[1]means black
chessboard[2]means king
*/
/*return the next position */
inline CHESS Move(const CHESS position,const int horizontal,const int vertical)
{
	return vertical ?
		(position << (3 + horizontal + (1^ (!(kEven&position))))):
		(position >> (3 + (1 ^ horizontal) + (!(kEven&position))));
}
/*return the next position of the next position*/
inline CHESS Jump(const CHESS position,const  int horizontal,const int vertical)
{
	return vertical ?
		(position << (7 + (horizontal << 1))):
		(position >> (7 + ((horizontal ^ 1) << 1)));
}
/*to count how many 1 in its  binary number*/
inline int Count(CHESS chessboard) {
	chessboard = ((chessboard >> 1) & 0x55555555) + (chessboard & 0x55555555);
	chessboard = ((chessboard >> 2) & 0x33333333) + (chessboard & 0x33333333);
	chessboard = ((chessboard >> 4) & 0x0f0f0f0f) + (chessboard & 0x0f0f0f0f);
	chessboard = ((chessboard >> 8) & 0x00ff00ff) + (chessboard & 0x00ff00ff);
	return (chessboard >> 16) + (chessboard & 0x0000ffff);
}


/*****************DEBUG************/
inline void print(CHESS state)
{
	printf("\n****************");
	fflush(stdout);
	for (int j = 0; j < 8; j++)
	{
		for (int i = 0; i < 4; i++)
		{
			if (i != 3&&(j&1))
			{
				printf("0");
				fflush(stdout);
			}
			printf("%d", (state&(1 << (CHESS) (4 * (7-j) + 3-i ))) ? 1 : 0);
			fflush(stdout);
			if (i != 3&&!(j&1))
			{
				printf("0");
				fflush(stdout);
			}
		}
		if(j!=7) printf("\n");
	}
	printf("\n****************\n\n");
	fflush(stdout);
	printf("\n");
	fflush(stdout);
}
/*************************************/


/*********PART 2 FIND WAYS TO GO**********/
/*possible jump*/
/*the list to save the moving method and its index*/
/*
for each side and chessboard statement
we generate a list including every possible single move or every possible jump
and return its size
*/
typedef struct List
{
	CHESS method[3];
	int value;
	int type;
}LIST;
LIST list[MAXLS];
/*key saves the index of a rank in one node*/
int key[MAXLS];
int index;
/*hash the chessboard to find its interval of key*/
typedef struct Hashlist
{
	int start;
	int end;
	CHESS chessboard[3];
}HASH;
HASH hash[2][MOD][10];
int total[2][MOD];
inline int Hash(CHESS chessboard[])
{
	return ((chessboard[WHITE] >> 3) ^ chessboard[KING] ^ (chessboard[BLACK] << 1)) % MOD;
}
HASH * HashFind(const CHESS chessboard[],int side)
{
	int pos = Hash(chessboard);
	if (!total[side][pos]) return NULL;
	for (int i = 0; i < total[side][pos]; i++)
	{
		HASH *temp = &hash[side][pos][i];
		if (temp->chessboard[WHITE] == chessboard[WHITE]
			&& temp->chessboard[BLACK] == chessboard[BLACK]
			&& temp->chessboard[KING] == chessboard[KING])
		{
			return temp;
		}
	}
	return NULL;
}
HASH *HashPush(CHESS chessboard[], int start, int end,int side)
{
	int pos = Hash(chessboard);
	total[side][pos]++;
	HASH *node = &hash[side][pos][total[side][pos]];
	node->start = start;
	node->end = end;
	node->chessboard[WHITE] = chessboard[WHITE];
	node->chessboard[BLACK] = chessboard[BLACK];
	node->chessboard[KING] = chessboard[KING];
	return node;
}

/*the queue to bfs and its head and tail*/
/*
queue[i][0]saves chessboard of present statement of all my chess
queue[i][1]saves chessboard of beaten enemy
queue[i][2]saves chessboard of present extending position
*/
CHESS queue[150][3];
int head = 1, tail = 0;

/*reset a queue*/
inline void QueueReset(void)
{ 
	head = 1; 
	tail = 0; 
}

/*push a node in the queue*/
inline void QueuePush(const CHESS state,const CHESS bridge,const CHESS position)
{
	++tail;
	queue[tail][MINE] = state;
	queue[tail][ENEMY] = bridge;
	queue[tail][KING] = position;
}

/*pop a node off the queue */
inline void QueuePop(CHESS *state, CHESS *bridge, CHESS *position)
{
	(*state) = queue[head][MINE];
	(*bridge) = queue[head][ENEMY];
	(*position) = queue[head][KING];
	head++;
}

/*find possible jump in one direction*/
inline void OneDirectionJump(const CHESS enemy,const CHESS state,const CHESS bridge,const CHESS position,const int horizontal,const int vertical)
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

/*find all possible jump*/
inline int  FindPossibleJump(const CHESS chessboard[],const int side)
{
	int start = index;
	CHESS generate = chessboard[side];
	CHESS state = chessboard[side];
	CHESS bridge=0, position=0;
	QueueReset();
	while (generate)
	{
		position = generate & ((~generate) + 1);
		QueuePush(state, 0, position);
		generate ^= position;
	}
	while (head <= tail)
	{
		QueuePop(&state, &bridge, &position);
		OneDirectionJump(chessboard[side ^ 1], state, bridge, position, side^1, side^1);
		OneDirectionJump(chessboard[side ^ 1], state, bridge, position, side, side^1);
		OneDirectionJump(chessboard[side ^ 1], state, bridge, position, side^1, side);
		OneDirectionJump(chessboard[side ^ 1], state, bridge, position, side, side);
	}
	if (!queue[tail][ENEMY]) return 0;
	while (Count(queue[--head][ENEMY]) ==Count(queue[tail][ENEMY]));
	while ((++head) <= tail)
	{
		++index;
		key[index] = index;
		list[index].method[side] = queue[head][MINE];
		list[index].method[side ^ 1] = chessboard[side^1]^queue[head][ENEMY];
		list[index].method[KING] = chessboard[KING] ^ (chessboard[KING] & queue[head][ENEMY]);
		list[index].method[KING] = list[index].method[KING] & (chessboard[side] ^ queue[head][MINE]) ? list[index].method[KING] ^ (chessboard[side] ^ queue[head][MINE]) : list[index].method[KING];
	}
	return index-start;
}

/*possible single move*/
inline void OneDirectionMove(const CHESS chessboard[], const CHESS position, const int side, const int horizontal, int vertical)
{
	if (!(position&kCutMove[horizontal][vertical]))
	{
		return;
	}
	CHESS move = Move(position, horizontal, vertical);
	if (!(move&(~(chessboard[side]|chessboard[side^1])))) return;
	index++;
	move ^= position;
	key[index] = index;
	list[index].method[side] = chessboard[side] ^ move;
	list[index].method[side ^ 1] = chessboard[side ^ 1];
	list[index].method[KING] = (chessboard[KING] & position) ? chessboard[KING] ^ move : chessboard[KING];
}
inline int FindPossibleMove(const CHESS chessboard[],const int side)
{
	int start = index;
	CHESS generate = chessboard[side];
	while (generate)
	{
		CHESS position = generate & ((~generate) + 1);
		OneDirectionMove(chessboard, position, side, side^1, side^1);
		OneDirectionMove(chessboard, position, side, side, side ^ 1);
		generate ^= position;
	}
	generate = chessboard[side] & chessboard[KING];
	while (generate)
	{
		CHESS position = generate & ((~generate) + 1);
		OneDirectionMove(chessboard, position, side, side^1, side);
		OneDirectionMove(chessboard, position, side, side, side);
		generate ^= position;
	}
	return index-start;
}

/*********PART 3 SEARCH**************/

/*search*/
/*CHESS data*/
CHESS output[2];
inline int Evaluate(const CHESS chessboard[])
{
	/*so how do we evaluate the state*/
	/*this is such a really hard question*/
	




	return 0;
}


inline int CheckOut(CHESS chessboard)
{


	return 0;
}


void ListSort(int start, int end,int side)
{
	int i = start;
	int j = end;
	int mid = list[key[(start + end) / 2]].value;
	while (i <= j)
	{
		while (list[key[i]].value < mid) i++;
		while (list[key[j]].value > mid) j--;
		if (i <= j)
		{ 
			int temp = key[i];
			key[i] = key[j];
			key[j] = temp;
			i++; j--;
		}
	}
	if (start < j)  ListSort(start, j, side);
	if (i < end)  ListSort(i, end, side);
}




int AlphaBeta(const int depth, int alpha, int beta,const CHESS chessboard[],const int side)
{
	if (depth == 0) {
		return Evaluate(chessboard);
	}
	HASH *node=NULL;
	node = HashFind(chessboard, side);
	if(node==NULL)
	{
		int start = index;
		if (FindPossibleJump(chessboard, side) || FindPossibleMove(chessboard, side))
		{
			node = HashPush(chessboard, start + 1, index,side);
			for (int i = node->start; i <=node->end; i++)
			{
				list[i].value = Evaluate(list[i].method);
			}
			sort(node->start, node->end);
		}
		else
		{
			return -INFINITY;
		}
	}
	/*from start+1 to index,we should sort the number*/
	for(int i=node->start;i<=node->end;i++)
	{
		int pos = key[i];
		int value = -AlphaBeta(depth - 1, -beta, -alpha,list[pos].method,side^1);
		list[pos].value = value;
		if (value >= beta) 
		{
			sort(node->start + 1, i);
			return beta;
		}
		if (value > alpha)
		{
			alpha = value;
			output[side] = list[key[i]].method[side];
			output[side ^ 1] = list[key[i]].method[side ^ 1];
		}
	}
	sort(node->start+1,)
	return alpha;
}

inline int Transform(CHESS state)
{
	int temp = 0;
	while (!(state&(1 << temp))) temp++;
	return (temp<<1) + (((temp >> 2) & 1) ^ 1);
}

int path[50];

inline void OneDirectionPrint(CHESS * position, CHESS *bridge, int horizontal, int vertical)
{
	if (!(((*position)&kCutMove[horizontal][vertical]) && ((*position)&kCutJump[horizontal][vertical])))
	{
		return;
	}
	if (Move(*position, horizontal, vertical)&(*bridge))
	{
		(*bridge) ^= Move(*position, 1, 1);
		(*position) = Jump(*position, 1, 1);
		int end = Transform(*position);
		printf(" %d,%d", end >> 3, end & 7);
		fflush(stdout);
	}
	return;
}
inline void Print(CHESS chessboard[],int side)
{
	int cnt = 2;
	CHESS temp = chessboard[side] ^ output[side];
	CHESS bridge = chessboard[side ^ 1] ^ output[side ^ 1];
	int start = Transform(chessboard[side] & temp);
	int end = Transform(output[side] & temp);
	if (bridge)
	{
		printf("%d %d,%d", Count(bridge) + 1, start >> 3, start & 7);
		CHESS position = chessboard[side] & temp;
		while (bridge)
		{
			OneDirectionPrint(&position, &bridge, 1, 0);
			OneDirectionPrint(&position, &bridge, 1, 1);
			OneDirectionPrint(&position, &bridge, 0, 1);
			OneDirectionPrint(&position, &bridge, 0, 0);
		}
	}
	else
	{
		printf("%d %d,%d %d,%d", cnt,start>>3,start&7,end>>3,end&7);
		fflush(stdout);
	}
	return;
}


/**********PART 4 STDIN/STDOUT**************/
void Search(CHESS chessboard[],const int side)
{
	AlphaBeta(6, -INFINITY, INFINITY, chessboard, side);
	chessboard[2] |= chessboard[side] & kKing;
	Print(chessboard, side);
	return;
}

inline CHESS Locate(int x, int y)
{
	return (1<< ((y << 2) | (x >> 1)));
}
void Work(int side)
{

	/*chessboard[0]means white */
	/*chessboard[1]means black*/
	/*chessboard[2]means king*/
	CHESS chessboard[3];
	printf("OK\n");
	char order[10];
	while (1)
	{
		scanf("%s", order);/*recieve a order*/
		if (order[0] == 'T')
		{
			Search(chessboard,side);
			continue;
		}
		if (order[0] == 'P')
		{
			int number;
			scanf("%d", &number);
			int y[40], x[40];
			for (int i = 1; i <= number; i++)
			{
				scanf("%d,%d", &y[i], &x[i]);
			}
			CHESS start = Locate(x[1], y[1]);
			CHESS end = Locate(x[2], y[2]);
			chessboard[side ^ 1] ^= start | end;
			chessboard[2] = start&chessboard[2] ? (chessboard[2] ^ (start | end)) : chessboard[2];
			chessboard[2] |= end&kKing;
			if ((x[1] - x[2])*(x[1] - x[2])*(y[1] - x[2])*(y[1] - x[2]) != 1)
			{
				for (int i = 2; i <= number; i++)
				{
					int col = (y[i] + y[i - 1]) >> 1;
					int row = (x[i] + x[i - 1]) >> 1;
					chessboard[side] ^= Locate(row, col);
					chessboard[2] ^= chessboard[2] & Locate(row, col);
				}
			}
			continue;
		}
		if (order[0] == 'E')
		{
			return;
		}
 	}
	return;
}

int main()
{
	int my_side;
	scanf("START %d", &my_side);
	Work(my_side);
	return 0;
}

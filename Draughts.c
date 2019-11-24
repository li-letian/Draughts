#include<stdio.h>
#include<string.h>
/*from MediocreKonjac*/
#define CHESS unsigned long long
#define MAXLIST 20
#define INFINITY 0x3f3f3f3f
/*suppose the chessboard looks like
						7
						6
						5
						4
						3
						2
						1
						0
7 6 5 4 3 2 1 0
and the white chess is beneath the black chess
(so this is just a reverse of the required key board
and we can simply calculate the right position
and my chessboard looks like a unsigned long long integer
and the bit goes like
63 62 ...........56
..........................8
7 6 5 4 3 2 1 0

*/
/**********PART 1 PREWORK*************/
/*constant*/
const int kMaxSize = 8;
const CHESS kCutColumn[2] = { 0xfefefefefefefefe,0x7f7f7f7f7f7f7f7f };
const CHESS kCutDoubleColumn[2] = { 0xfcfcfcfcfcfcfcfc,0x3f3f3f3f3f3f3f3f };
const CHESS kKingRow = 0xff000000000000ff;
const CHESS kAllChessBoard = 0xffffffffffffffff;




/*generate a specific direction bitboard move or jump*/

/*suppose
the value of horizontal:0 means step right, 1 means step left
the value of vertical:0 means step back, 1 means step forward*/
/*chessboard[0]means white */
/*chessboard[1]means black*/
/*chessboard[2]means king*/
inline CHESS Move(const CHESS chessboard,const int horizontal,const int vertical)
{
	return (vertical) ?  (chessboard << ( horizontal? 9 : 7 ))&kAllChessBoard: (chessboard >> (horizontal? 7 : 9))&kAllChessBoard;
}
inline CHESS Jump(const CHESS chessboard,const  int horizontal,const int vertical)
{
	return (vertical) ? (chessboard << (horizontal ? 18 : 14))&kAllChessBoard : (chessboard >> (horizontal ? 14 : 18))&kAllChessBoard;
}


/*****************DEBUG************/
inline void print(CHESS state)
{

	printf("\n****************\n\n");
	for (int i = 0; i < 7; i++)
	{
		for (int j = 0; j < 7; j++)
		{
			printf("%d", state&(1 << (8 * (7 - i) + 7 - j)) ? 1 : 0);
		}
		printf("\n");
	}
}
/*************************************/


/*********PART 2 FIND WAYS TO GO**********/

/*possible jump*/
/*
queue[i][0]saves chessboard of present statement of all my chess
queue[i][1]saves chessboard of beaten enemy
queue[i][2]saves chessboard of present extending location
queue[i][3]saves numbers of the beaten enemy
*/
CHESS queue[150][4];
int head = 1, tail = 0;
inline void QueueReset()
{ 
	head = 1; 
	tail = 0; 
}
inline void QueuePush(const CHESS state,const CHESS bridge,const CHESS location,const CHESS number)
{
	++tail;
	queue[tail][0] = state;
	queue[tail][1] = bridge;
	queue[tail][2] = location;
	queue[tail][3] = number;
}
inline void QueuePop(CHESS *state, CHESS *bridge, CHESS *location,CHESS *number)
{
	(*state) = queue[head][0];
	(*bridge) = queue[head][1];
	(*location) = queue[head][2];
	(*number) = queue[head][3];
	head++;
}
inline void OneDirectionJump(const CHESS enemy,const CHESS state,const CHESS bridge,const CHESS location,CHESS number,const int horizontal,const int vertical)
{
	if(((Move(location,horizontal,vertical)&kCutColumn[horizontal^1])&(enemy^bridge))
		&((Jump(location, horizontal, vertical)&kCutDoubleColumn[horizontal ^ 1])&(~(state | enemy))))
	{
		QueuePush(state ^ (location | Jump(location, horizontal, vertical)), bridge | Move(location, horizontal, vertical), Jump(location, horizontal, vertical),number+1);
	}
}
inline int  FindPossibleJump(CHESS list[][3],const CHESS chessboard[],const int side)
{
	int index = 0;
	CHESS state = chessboard[side];
	CHESS bridge, location, number;
	QueueReset();
	while (state)
	{
		CHESS position = state ^ (state - 1);
		position = position ^ (position >> 1);
		QueuePush(state, 0, position,0);
	}
	while (head <= tail)
	{
		QueuePop(&state, &bridge, &location,&number);
		OneDirectionJump(chessboard[side ^ 1], state, bridge, location, number, 1, 1);
		OneDirectionJump(chessboard[side ^ 1], state, bridge, location, number, 0, 1);
		OneDirectionJump(chessboard[side ^ 1], state, bridge, location, number, 1, 0);
		OneDirectionJump(chessboard[side ^ 1], state, bridge, location, number, 0, 0);
	}
	if (!queue[tail][3]) return 0;
	while (queue[--head][3] == queue[tail][3]);
	while ((++head) <= tail)
	{
		index++;
		list[index][side] = queue[head][0];
		list[index][side ^ 1] = chessboard[side^1]^queue[head][1];
		list[index][2] = chessboard[2] ^ (chessboard[2] & queue[head][1]);
		list[index][2] = list[index][2] & (chessboard[side] ^ queue[head][0]) ? list[index][2] ^ (chessboard[side] ^ queue[head][0]) : list[index][2];
	}
	return index;
}

/*possible single move*/
/*for each side and chessboard statement,it can generate a list including every possible single move and return its size*/
/*suppose 
0 means white,1 means black
0 means step right, 1 means step left
0 means step back, 1 means step forward*/
inline void OneDirectionMove(int *index,CHESS list[][3],const CHESS chessboard[], const int side,const int horizontal)
{
	CHESS move= ((Move(chessboard[side], horizontal, side ^ 1)&kCutColumn[horizontal^1])&(~chessboard[side ^ 1]))&kAllChessBoard;
	while (move)
	{
		CHESS position;
		position = move ^ (move - 1);
		position = position ^ (position >> 1);
		move = move ^ position;
		position = position | Move(position, horizontal^1, side);
		(*index)++;
		list[*index][side] = chessboard[side] ^ position;
		list[*index][side ^ 1] = chessboard[side ^ 1];
		list[*index][2] = (chessboard[2] & position) ? chessboard[2] ^ position : chessboard[2];
	}
}
inline void KingExtralMove(int *index, CHESS list[][3], const CHESS chessboard[], const int side, const int horizontal)
{
	CHESS move = ((Move(chessboard[side]&chessboard[2], horizontal, side)&kCutColumn[horizontal ^ 1])&(~chessboard[side ^ 1]))&kAllChessBoard;
	while (move)
	{
		CHESS position;
		position = move ^ (move - 1);
		position = position ^ (position >> 1);
		move = move ^ position;
		position = position | Move(position, horizontal ^ 1, side^1);
		(*index)++;
		list[*index][side] = chessboard[side] ^ position;
		list[*index][side ^ 1] = chessboard[side ^ 1];
		list[*index][2] =chessboard[2] ^ position;
	}
}
inline int FindPossibleMove(CHESS list[][3],const CHESS chessboard[],const int side)
{
	int index = 0;
	OneDirectionMove(&index, list, chessboard, side, 1);
	OneDirectionMove(&index, list, chessboard, side, 0);
	KingExtralMove(&index, list, chessboard, side, 1);
	KingExtralMove(&index, list, chessboard, side, 0);
	return index;
}

/*********PART 3 SEARCH**************/

/*search*/

CHESS output[2];
inline int Evaluate(const CHESS chessboard[])
{
	
	return 0;
}
int AlphaBeta(const int depth, int alpha, int beta,const CHESS chessboard[],const int side)
{
	if (depth == 0) {
		return Evaluate(chessboard);
	}
	CHESS list[MAXLIST][3];
	int index = 0;
	if (!(index=FindPossibleJump(list, chessboard, side)))
	{
		index=FindPossibleMove(list, chessboard, side);
	}
	while (index--) 
	{
		int value = -AlphaBeta(depth - 1, -beta, -alpha,list[index],side^1);
		if (value >= beta) 
		{
			return beta;
		}
		if (value > alpha)
		{
			alpha = value;
			output[side] = list[index][side];
			output[side ^ 1] = list[index][side ^ 1];
		}
	}
	return alpha;
}

void Print()
{


}


/**********PART 4 STDIN/STDOUT**************/
void Search(CHESS *chessboard,const int side)
{
	AlphaBeta(6, -INFINITY, INFINITY, chessboard, side);
	Print();
}

inline CHESS Locate(int x, int y)
{
	return ((CHESS)1) << (x + 8 * y);
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
			// search();
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
			chessboard[side] = chessboard[side] ^ (Locate(x[1], y[1]) | Locate(x[number], y[number]));
			chessboard[2] = Locate(x[1], y[1])&chessboard[2] ? chessboard[2] ^ (Locate(x[1], y[1]) | Locate(x[number], y[number])) : chessboard[2];
			if ((x[1] - x[2])*(x[1] - x[2])*(y[1] - x[2])*(y[1] - x[2]) != 1)
			{
				for (int i = 2; i <= number; i++)
				{
					int col = (y[i] + y[i - 1]) >> 1;
					int row = (x[i] + x[i - 1]) >> 1;
					chessboard[side ^ 1] = chessboard[side ^ 1] ^ Locate(row, col);
					chessboard[2] = chessboard[2] ^ (chessboard[2] & Locate(row, col));
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
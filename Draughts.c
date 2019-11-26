#include<stdio.h>
#include<string.h>
/*from MediocreKonjac*/
#define CHESS unsigned long long
#define MAXLIST 1000010
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
const CHESS kCutColumn[2] = { 0xfefefefefefefefe,0x7f7f7f7f7f7f7f7f };
const CHESS kCutDoubleColumn[2] = { 0xfcfcfcfcfcfcfcfc,0x3f3f3f3f3f3f3f3f };
const CHESS kKingRow = 0xff000000000000ff;
const CHESS kAllChessBoard = 0xffffffffffffffff;

/*generate a specific direction bitboard move or jump*/

/*
suppose
the value of horizontal:0 means step right, 1 means step left
the value of vertical:0 means step back, 1 means step forward
chessboard[0]means white 
chessboard[1]means black
chessboard[2]means king
*/
/*return a next position */
inline CHESS Move(const CHESS chessboard,const int horizontal,const int vertical)
{
	return (vertical) ?  (chessboard << ( horizontal? 9 : 7 ))&kAllChessBoard: (chessboard >> (horizontal? 7 : 9))&kAllChessBoard;
}

/*return the next position of the next position*/
inline CHESS Jump(const CHESS chessboard,const  int horizontal,const int vertical)
{
	return (vertical) ? (chessboard << (horizontal ? 18 : 14))&kAllChessBoard : (chessboard >> (horizontal ? 14 : 18))&kAllChessBoard;
}

/*to count how many 1 in its  binary number*/
inline int Count(CHESS chessboard)
{
	chessboard = ((chessboard >> 1) & 0x5555555555555555) + (chessboard & 0x5555555555555555);
	chessboard = ((chessboard >> 2) & 0x3333333333333333) + (chessboard & 0x3333333333333333);
	chessboard = ((chessboard >> 4) & 0x0f0f0f0f0f0f0f0f) + (chessboard & 0x0f0f0f0f0f0f0f0f);
	chessboard = ((chessboard >> 8) & 0x00ff00ff00ff00ff) + (chessboard & 0x00ff00ff00ff00ff);
	chessboard = ((chessboard >> 16) & 0x0000ffff0000ffff) + (chessboard & 0x0000ffff0000ffff);
	return ((chessboard >> 32) + (chessboard & 0x00000000ffffffff));
}


/*****************DEBUG************/
inline void print(CHESS state)
{

	printf("\n****************\n\n");
	for (int i = 0; i < 7; i++)
	{
		for (int j = 0; j < 7; j++)
		{
			printf("%d", (state&(1 << (CHESS) (8 * (7 - i) + 7 - j))) ? 1 : 0);
		}
		printf("\n");
	}
}
/*************************************/


/*********PART 2 FIND WAYS TO GO**********/

/*possible jump*/

/*global variables*/

/*the list to save the moving method and its index*/
/*
for each side and chessboard statement
we generate a list including every possible single move or every possible jump
and return its size
*/
CHESS list[MAXLIST][3];
int index;

/*the queue to bfs and its head and tail*/
/*
queue[i][0]saves chessboard of present statement of all my chess
queue[i][1]saves chessboard of beaten enemy
queue[i][2]saves chessboard of present extending location
*/
CHESS queue[150][3];
int head = 1, tail = 0;

/*reset a queue*/
inline void QueueReset()
{ 
	head = 1; 
	tail = 0; 
}

/*push a node in the queue*/
inline void QueuePush(const CHESS state,const CHESS bridge,const CHESS location)
{
	++tail;
	queue[tail][0] = state;
	queue[tail][1] = bridge;
	queue[tail][2] = location;
}

/*pop a node off the queue */
inline void QueuePop(CHESS *state, CHESS *bridge, CHESS *location)
{
	(*state) = queue[head][0];
	(*bridge) = queue[head][1];
	(*location) = queue[head][2];
	head++;
}

/*find possible jump in one direction*/
inline void OneDirectionJump(const CHESS enemy,const CHESS state,const CHESS bridge,const CHESS location,const int horizontal,const int vertical)
{
	if(((Move(location,horizontal,vertical)&kCutColumn[horizontal^1])&(enemy^bridge))
		&((Jump(location, horizontal, vertical)&kCutDoubleColumn[horizontal ^ 1])&(~(state | enemy))))
	{
		QueuePush(state ^ (location | Jump(location, horizontal, vertical)), bridge | Move(location, horizontal, vertical), Jump(location, horizontal, vertical));
	}
}

/*find all possible jump*/
inline int  FindPossibleJump(const CHESS chessboard[],const int side)
{
	int start = index;
	CHESS state = chessboard[side];
	CHESS bridge=0, location=0;
	QueueReset();
	while (state)
	{
		CHESS position = state & ((~state) + 1);
		state ^= position;
		QueuePush(state, 0, position);
	}
	while (head <= tail)
	{
		QueuePop(&state, &bridge, &location);
		OneDirectionJump(chessboard[side ^ 1], state, bridge, location, 1, 1);
		OneDirectionJump(chessboard[side ^ 1], state, bridge, location, 0, 1);
		OneDirectionJump(chessboard[side ^ 1], state, bridge, location, 1, 0);
		OneDirectionJump(chessboard[side ^ 1], state, bridge, location, 0, 0);
	}
	if (!queue[tail][1]) return 0;
	while (Count(queue[--head][1]) ==Count(queue[tail][1]));
	while ((++head) <= tail)
	{
		index++;
		list[index][side] = queue[head][0];
		list[index][side ^ 1] = chessboard[side^1]^queue[head][1];
		list[index][2] = chessboard[2] ^ (chessboard[2] & queue[head][1]);
		list[index][2] = list[index][2] & (chessboard[side] ^ queue[head][0]) ? list[index][2] ^ (chessboard[side] ^ queue[head][0]) : list[index][2];
	}
	return index-start;
}

/*possible single move*/
inline void OneDirectionMove(const CHESS chessboard[], const int side,const int horizontal)
{
	CHESS move= ((Move(chessboard[side], horizontal, side ^ 1)&kCutColumn[horizontal^1])&(~chessboard[side ^ 1]))&kAllChessBoard;
	while (move)
	{
		CHESS position = move & ((~move) + 1);
		move ^= position;
		position |= Move(position, horizontal^1, side);
		index++;
		list[index][side] = chessboard[side] ^ position;
		list[index][side ^ 1] = chessboard[side ^ 1];
		list[index][2] = (chessboard[2] & position) ? chessboard[2] ^ position : chessboard[2];
	}
}


inline void KingExtralMove(const CHESS chessboard[], const int side, const int horizontal)
{
	CHESS move = ((Move(chessboard[side]&chessboard[2], horizontal, side)&kCutColumn[horizontal ^ 1])&(~chessboard[side ^ 1]))&kAllChessBoard;
	while (move)
	{
		CHESS position;
		position = move ^ (move - 1);
		position ^= (position >> 1);
		move ^= position;
		position |= Move(position, horizontal ^ 1, side^1);
		index++;
		list[index][side] = chessboard[side] ^ position;
		list[index][side ^ 1] = chessboard[side ^ 1];
		list[index][2] =chessboard[2] ^ position;
	}
}

inline int FindPossibleMove(const CHESS chessboard[],const int side)
{
	int start = index;
	OneDirectionMove(chessboard, side, 1);
	OneDirectionMove(chessboard, side, 0);
	KingExtralMove(chessboard, side, 1);
	KingExtralMove(chessboard, side, 0);
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
int AlphaBeta(const int depth, int alpha, int beta,const CHESS chessboard[],const int side)
{
	/*check out whether it is a searched statement*/
	if (depth == 0) {
		return Evaluate(chessboard);
	}
	int start=index;
	if ((! FindPossibleJump(chessboard, side)) && (! FindPossibleMove(chessboard, side)))
	{
		//no ways to go ,this side has lost,you can just return a value of total win or total lost
	}
	/*from start+1 to index,we should sort the number*/
	for(int i=start+1;i<=index;i++)
	{
		int value = -AlphaBeta(depth - 1, -beta, -alpha,list[i],side^1);
		if (value >= beta) 
		{
			return beta;
		}
		if (value > alpha)
		{
			alpha = value;
			output[side] = list[i][side];
			output[side ^ 1] = list[i][side ^ 1];
		}
	}
	/*save this state for future statement?*/
	return alpha;
}

inline int Transform(CHESS state)
{
	int temp = 0;
	while (!(state&(1 << temp))) ++temp;
	return temp;
}

int path[50];
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
			if (Move(position, 1, 1)&bridge)
			{
				bridge ^= Move(position, 1, 1);
				position = Jump(position, 1, 1);
				end = Transform(position);
				printf(" %d,%d", end >> 3, end & 7);
				fflush(stdout);
				continue;
			}
			if(Move(position, 0, 1)&bridge)
			{
				bridge ^= Move(position, 0, 1);
				position = Jump(position, 0, 1);
				end = Transform(position);
				printf(" %d,%d", end >> 3, end & 7);
				fflush(stdout);
				continue;
			}
			if (Move(position, 1, 0)&bridge)
			{
				bridge ^= Move(position, 1, 0);
				position = Jump(position, 1, 0);
				end = Transform(position);
				printf(" %d,%d", end >> 3, end & 7);
				fflush(stdout);
				continue;
			}
			if (Move(position, 0, 0)&bridge)
			{
				bridge ^= Move(position, 0, 0);
				position = Jump(position, 0, 0);
				end = Transform(position);
				printf(" %d,%d", end >> 3, end & 7);
				fflush(stdout);
				continue;
			}
		}
	}
	else
	{
		printf("%d %d,%d %d,%d", cnt,start>>3,start&7,end>>3,end&8);
		fflush(stdout);
	}


}


/**********PART 4 STDIN/STDOUT**************/
void Search(CHESS chessboard[],const int side)
{
	AlphaBeta(6, -INFINITY, INFINITY, chessboard, side);
	chessboard[2] |= chessboard[side] & kKingRow;
	Print(chessboard, side);
}

inline CHESS Locate(int x, int y)
{
	return ((CHESS)1) << ((y << 3) | x);
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
			chessboard[side] ^= (Locate(x[1], y[1]) | Locate(x[number], y[number]));
			chessboard[2] = Locate(x[1], y[1])&chessboard[2] ? chessboard[2] ^ (Locate(x[1], y[1]) | Locate(x[number], y[number])) : chessboard[2];
			if ((x[1] - x[2])*(x[1] - x[2])*(y[1] - x[2])*(y[1] - x[2]) != 1)
			{
				for (int i = 2; i <= number; i++)
				{
					int col = (y[i] + y[i - 1]) >> 1;
					int row = (x[i] + x[i - 1]) >> 1;
					chessboard[side ^ 1] ^= Locate(row, col);
					chessboard[2] ^= (chessboard[2] & Locate(row, col));
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

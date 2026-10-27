// Notes to self : 

// TODO
// 1.  DONE Print functions: single bitboard as 8x8 grid, and full board with piece letters
// 2.  DONE Decide extra board data: occupancy bitboards (white, black, all) and square-to-piece array
// 3.  DONE FEN parsing
// 4.  DONE (ig) Move representation: from, to, promotion, flags; plus text conversion (e2e4)
// 5.  Attack generation: leapers (knight, king, pawn) via tables, then sliders (rook, bishop, queen)
// 6.  "Is this square attacked?" function
// 7.  Pseudo-legal move generation, including castling, en passant, promotion
// 8.  Make move (copy-make first, undo later if needed)
// 9.  Legality filter: discard moves that leave own king attacked
// 10. Perft on standard test positions, use perft divide to find bugs
// 11. Evaluation: material, then piece-square tables, side-to-move perspective
// 12. Negamax, then alpha-beta, then move ordering
// 13. UCI loop, then connect to Cute Chess

#include <ctype.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// using 64 bit integer for board representation otherwise known as bitboard
typedef uint64_t U64;
// 16 bits used in the moves struct
typedef uint16_t U16;

// bit manipulation macros inspired by (https://www.youtube.com/watch?v=A6Eu8xhwMkY)

// to check whether a square is occupied in a bitboard
#define get_bit(bitboard, index) ((bitboard) & (1ULL << (index)))  // Returns non-zero if the bit at 'index' is set in 'bitboard' (the AND with the single-1 mask overlaps), else 0 (the 1s fall on different squares).
// to set a square (turn the bit on) in a bitboard, in place
#define set_bit(bitboard, index) ((bitboard) |= (1ULL << (index)))  // Turns on the bit at 'index' directly in 'bitboard' (|= ORs in the single-1 mask, so that square becomes 1 and all other bits stay unchanged).
// to clear a square (turn the bit off) in a bitboard, in place (used different approach than video)
#define pop_bit(bitboard, index) ((bitboard) &= ~(1ULL << (index)))  // Clears the bit at 'index' in place: ~(1ULL << index) is a mask of all 1s with a single 0 at that square, so &= forces that bit to 0 and leaves the other 63 unchanged (safe even if the bit was already 0).

// packs from square, to square, and the code (in moves struct) to one 16-bit integer
#define encode_move(from, to, code) ((U16) ((from) | ((to) << 6) | ((code) << 12)))
// gets the from square from the integer made by encode_move
#define get_from(encoded_move) ((encoded_move) & 0x3F)  // 0x3F = 0b111111
// gets the to square from the integer made by encode_move
#define get_to(encoded_move) (((encoded_move) >> 6) & (0x3F))
// gets the code from the integer made by encode_move
#define get_code(encoded_move) (((encoded_move) >> 12) & (0xF))  // since code is 4 bits we make the mask 0xF = 0b1111

// here move is the integer returned by the encode_move
#define is_capture(move)       ((get_code(move)) & 0x4)  // returns 4 for true and zero for false
#define is_promotion(move)     ((get_code(move)) & 0x8)  // returns 8 for true and zero for false
#define is_en_passant(move)    ((get_code(move)) == EN_PASSANT)  // returns 1 for en_passant
#define is_double_push(move)   ((get_code(move)) == DOUBLE_PUSH)  // returns 1 for double_push otherwise 0
#define is_castle(move)        (((get_code(move)) == KING_CASTLE) || ((get_code(move)) == QUEEN_CASTLE))  //  
#define promotion_piece(move)  ((get_code(move)) & 0x3)  // returns 0, 1, 2, 3 for knight, bishop, rook, queen respectively

// for the moves struct (the last 4 bits)
enum { MOVE_QUIET, DOUBLE_PUSH, KING_CASTLE, QUEEN_CASTLE, MOVE_CAPTURE, EN_PASSANT,
       KNIGHT_PROMOTION = 8, BISHOP_PROMOTION, ROOK_PROMOTION, QUEEN_PROMOTION,
       KNIGHT_PROMOTION_CAPTURE, BISHOP_PROMOTION_CAPTURE, ROOK_PROMOTION_CAPTURE, QUEEN_PROMOTION_CAPTURE };

// index will be used in set_start_position
// piece order matters: must match the letters string "PNBRQKpnbrqk" used when printing
enum { WHITE_PAWN, WHITE_KNIGHT, WHITE_BISHOP, WHITE_ROOK, WHITE_QUEEN, WHITE_KING,
       BLACK_PAWN, BLACK_KNIGHT, BLACK_BISHOP, BLACK_ROOK, BLACK_QUEEN, BLACK_KING,
       PIECE_COUNT };

// occupancies
enum { WHITE_OCC, BLACK_OCC, BOTH_OCC, OCC_COUNT };

// castling rights
enum { WHITE_KING_SIDE = 8, WHITE_QUEEN_SIDE = 4, BLACK_KING_SIDE = 2, BLACK_QUEEN_SIDE = 1 };

// index 0 is a1 and so on, following the bitboard.md
const char *square_names[64] = {
    "a1", "b1", "c1", "d1", "e1", "f1", "g1", "h1",
    "a2", "b2", "c2", "d2", "e2", "f2", "g2", "h2",
    "a3", "b3", "c3", "d3", "e3", "f3", "g3", "h3",
    "a4", "b4", "c4", "d4", "e4", "f4", "g4", "h4",
    "a5", "b5", "c5", "d5", "e5", "f5", "g5", "h5",
    "a6", "b6", "c6", "d6", "e6", "f6", "g6", "h6",
    "a7", "b7", "c7", "d7", "e7", "f7", "g7", "h7",
    "a8", "b8", "c8", "d8", "e8", "f8", "g8", "h8"
};

const char *piece_letters = "PNBRQKpnbrqk";

// Board struct
typedef struct {
    U64 bitboards[PIECE_COUNT];   // piece_count is at index 12 in enum  
    U64 occupancies[OCC_COUNT];   // indexed by WHITE_OCC, BLACK_OCC, BOTH_OCC
    U64 en_passant;               // bitboard with 1 where en passant is possible
    int castling_rights;          // 4 bits: white kingside, white queenside, black kingside, black queenside
    int fifty_move_rule_counter;  // a player can claim a draw if 50 consecutive moves have been completed by each player without any capture or pawn movement 
    int number_of_moves_counter;          
    bool white_turn;
} Board;

// Moves struct
typedef struct {
    U16 moves;

    // bits 0-5 used for "from square"
    // bits 6-11 used for "to square"
    // bits 12-15 is for special cases explained below

    // MOVE ENCODING (16 bits), from chessprogramming.org/Encoding_Moves
    //
    // bit:   15 14 13 12 | 11 10  9  8  7  6 |  5  4  3  2  1  0
    //        code (4)      to square (6)       from square (6)
    //
    // code bits: [ promotion | capture | special 1 | special 0 ]
    //
    // code  promo  capt  sp1  sp0   kind of move
    //  0     0      0     0    0    quiet move
    //  1     0      0     0    1    double pawn push
    //  2     0      0     1    0    king castle
    //  3     0      0     1    1    queen castle
    //  4     0      1     0    0    capture
    //  5     0      1     0    1    en passant capture
    //  6, 7  (unused)
    //  8     1      0     0    0    knight promotion
    //  9     1      0     0    1    bishop promotion
    // 10     1      0     1    0    rook promotion
    // 11     1      0     1    1    queen promotion
    // 12     1      1     0    0    knight promotion + capture
    // 13     1      1     0    1    bishop promotion + capture
    // 14     1      1     1    0    rook promotion + capture
    // 15     1      1     1    1    queen promotion + capture
    // 
    // we are taking advantage of the fact that 4 bits can store maximum 16 (0-15) numbers

} Moves;

// initialize variables in Board struct
void set_start_position(Board *pos)
{
    pos->bitboards[WHITE_PAWN]   = 0x000000000000FF00ULL;  // Hex is used instead of writing 64 binary digits: each hex character represents exactly 4 bits, so the full 64-bit board needs only 16 characters (2 per rank)  
    pos->bitboards[WHITE_KNIGHT] = 0x0000000000000042ULL;  // b1, g1
    pos->bitboards[WHITE_BISHOP] = 0x0000000000000024ULL;  // c1, f1
    pos->bitboards[WHITE_ROOK]   = 0x0000000000000081ULL;  // a1, h1
    pos->bitboards[WHITE_QUEEN]  = 0x0000000000000008ULL;  // d1
    pos->bitboards[WHITE_KING]   = 0x0000000000000010ULL;  // e1

    pos->bitboards[BLACK_PAWN]   = 0x00FF000000000000ULL;
    pos->bitboards[BLACK_KNIGHT] = 0x4200000000000000ULL;  // b8, g8
    pos->bitboards[BLACK_BISHOP] = 0x2400000000000000ULL;  // c8, f8
    pos->bitboards[BLACK_ROOK]   = 0x8100000000000000ULL;  // a8, h8
    pos->bitboards[BLACK_QUEEN]  = 0x0800000000000000ULL;  // d8
    pos->bitboards[BLACK_KING]   = 0x1000000000000000ULL;  // e8

    pos->white_turn = true;

    pos->castling_rights = 0xF;                             // 0xF = 0b1111, 0xF = all four rights available, a 0 bit means that right is lost
    pos->en_passant = 0x0000000000000000ULL;                // 1 represents the square where the capturing pawn will land after capturing

    pos->fifty_move_rule_counter = 0;                       // if no capture and pawn move is done till fifty moves the game is a draw
    pos->number_of_moves_counter = 1;                       // at start is 1
}

// sets 3 bitboards : white pieces, black pieces, full board
void rebuild_occupancies(Board *pos)
{
    pos->occupancies[WHITE_OCC] = 0ULL;
    pos->occupancies[BLACK_OCC] = 0ULL;
    pos->occupancies[BOTH_OCC]  = 0ULL;

    for (int piece = WHITE_PAWN; piece < BLACK_PAWN; piece++)
        pos->occupancies[WHITE_OCC] |= pos->bitboards[piece];

    for (int piece = BLACK_PAWN; piece < PIECE_COUNT; piece++)
        pos->occupancies[BLACK_OCC] |= pos->bitboards[piece];

    pos->occupancies[BOTH_OCC] = pos->occupancies[WHITE_OCC] | pos->occupancies[BLACK_OCC];
}

//  evaluation(const Board *pos)
// {
// 
// }

// loads a position from a FEN string into pos
void load_position_from_fen(Board *pos, const char *fen)
{
    // reset everything so nothing from a previous position survives
    *pos = (Board){0};

    int rank = 8, file = 0;  // for file 0 represents a file, 1 b file, ...

    int i = 0;  // we are declaring i outside the loop because after the pieces are set we will use it for other tasks

    // logic inspired by (https://www.youtube.com/watch?v=U4ogK0MIzqk&t=150s)
    for (int length_fen = strlen(fen); i < length_fen; i++)
    {
        
        // going to a file of the next rank
        if (fen[i] == '/')  // p[i] is defined as an exact syntactic equivalent to *(p + i); remember char * points to the first character and reads it till null terminator is reached; strings lwk don't make sense in c 
        {
            file = 0;
            rank--;
        }

        // if empty spaces, which are denoted by numbers in fen
        else if (isdigit(fen[i]))
        {
            int num = fen[i] - '0';  // converts the char number to an int number
            file += num;
        }

        else if (fen[i] == ' ')
        {
            break;  // we are breaking because now we know the pieces bitboards are set
        }

        // updating bitboards
        else 
        {
            int square = (rank - 1) * 8 + file;

            // check which piece is at the current square
            for (int j = 0, length_piece_letters = strlen(piece_letters); j < length_piece_letters; j++)
            {
                if (fen[i] == piece_letters[j])
                {
                    set_bit(pos->bitboards[j], square);  // indexing of the bitboards array and piece_letters string is same therefore both can use j
                    file++;
                    break;
                }
            }
        }
    }

    i++;

    // side to move
    pos->white_turn = (fen[i] == 'w');
    i += 2;

    // castling rights
    // check until the next space, so any combination works
    while (fen[i] != ' ' && fen[i] != '\0')
    {
        switch (fen[i])
        {
            case 'K': pos->castling_rights |= WHITE_KING_SIDE; break;
            case 'Q': pos->castling_rights |= WHITE_QUEEN_SIDE; break;
            case 'k': pos->castling_rights |= BLACK_KING_SIDE; break;
            case 'q': pos->castling_rights |= BLACK_QUEEN_SIDE; break;
            default: break;
        }
        i++;
    }
    i++;

    // en passant square
    if (fen[i] != '-')
    {
        int ep_file = fen[i] - 'a';      // 'e' - 'a' = 4
        int ep_rank = fen[i + 1] - '1';  // '3' - '1' = 2
        set_bit(pos->en_passant, ep_rank * 8 + ep_file);
        i += 2;
    }
    else
    {
        i++;
    }

    // halfmove clock and fullmove number, some FEN do not include these
    if (fen[i] == ' ')
    {
        i++;
        pos->fifty_move_rule_counter = atoi(&fen[i]);  // atoi stops reading at the first non-digit
        while (isdigit(fen[i])) i++;

        if (fen[i] == ' ')
        {
            i++;
            pos->number_of_moves_counter = atoi(&fen[i]);  // &fen[i] translates to pointer to the character at position i, which is fen + 1
        }
    }

    // get the occupancies from the bitboards
    rebuild_occupancies(pos);
}

// prints any bitboard as an 8x8 grid of 0s and 1s
void print_bitboard(U64 bitboard)
{
    printf("\n");

    for (int rank = 8; rank > 0; rank--)
    {
        printf("%d ", rank);
        for (int file = 0; file < 8; file++)
        {
            int square = (rank - 1) * 8 + file;
            printf(" %d", get_bit(bitboard, square) ? 1 : 0);
        }
        printf("\n");
    }
    printf("\n   a b c d e f g h\n");
    printf("\nhex: 0x%016llX\n\n", (unsigned long long)bitboard);
}

// prints the board using letters to symbolize pieces
void print_board(const Board *pos)
{
    printf("\n");

    // loop rank
    for (int rank = 8; rank > 0; rank--)
    {
        printf("%d ", rank);  // prints rank number
        // loop file
        for (int file = 0; file < 8; file++)
        {
            // use get_bit as a condition for if/else for every piece
            
            // index for get_bit function
            int square = (rank - 1) * 8 + file;
            char character = '.'; 

            // character = letters (which is stored in the letter string)
            for (int piece = 0; piece < PIECE_COUNT; piece++)    
            {
                if (get_bit(pos->bitboards[piece], square))
                {
                    character = piece_letters[piece];
                    break; 
                }
            }

            printf(" %c", character);
        }
        printf("\n");  // go to new line after every rank is printed
    }

    printf("\n   a b c d e f g h\n\n");
}

// prints moves
void print_moves(U16 *move)
{
    // from and to squares based on the indexing of bitboard.md
    // since moves are not implemented yet initializing a random move

    // move = encode_move(from_square, to_square, code);

    if (get_code(*move) == KNIGHT_PROMOTION || get_code(*move) == KNIGHT_PROMOTION_CAPTURE)
    {
        printf("%s", square_names[get_from(*move)]);
        printf("%s", square_names[get_to(*move)]) ;
        printf("n\n\n");
    }

    else if (get_code(*move) == BISHOP_PROMOTION || get_code(*move) == BISHOP_PROMOTION_CAPTURE)
    {
        printf("%s", square_names[get_from(*move)]);
        printf("%s", square_names[get_to(*move)]) ;
        printf("b\n\n");
    }

    else if (get_code(*move) == ROOK_PROMOTION || get_code(*move) == ROOK_PROMOTION_CAPTURE)
    {
        printf("%s", square_names[get_from(*move)]);
        printf("%s", square_names[get_to(*move)]) ;
        printf("r\n\n");
    }

    else if (get_code(*move) == QUEEN_PROMOTION || get_code(*move) == QUEEN_PROMOTION_CAPTURE)
    {
        printf("%s", square_names[get_from(*move)]);
        printf("%s", square_names[get_to(*move)]) ;
        printf("q\n\n");
    }

    else
    {
        printf("%s", square_names[get_from(*move)]);
        printf("%s\n\n", square_names[get_to(*move)]) ;   
    }
}

// prints the non-piece fields of a position
void print_state(const Board *pos)
{
    printf("side to move    : %s\n", pos->white_turn ? "white" : "black");
    printf("castling rights : %d  (0x%X)\n", pos->castling_rights, pos->castling_rights);
    printf("fifty move      : %d\n", pos->fifty_move_rule_counter);
    printf("move number     : %d\n", pos->number_of_moves_counter);
    printf("en passant      :\n");
    print_bitboard(pos->en_passant);
}

int main(void)
{
    Board board = {0}; // Initializing
    const char* fen = "r2q1rk1/pb1nbppp/1p2p3/2pp4/3P4/2NBP1B1/PPP1NPPP/R2Q1RK1 w - - 0 10";
    U16 move = 5900;  // rn hardcoded e2 to e4 for testing

    print_moves(&move);
    set_start_position(&board);
    rebuild_occupancies(&board);
    load_position_from_fen(&board, fen);
    print_board(&board);
    print_state(&board);
}

// References:

// YouTube:
// 1. https://www.youtube.com/@chessprogramming591
// 2. https://www.youtube.com/@BartekSpitza
// 3. https://www.youtube.com/@SebastianLague

// https://chessprogramming.org/
// https://www.w3schools.com/

// gemini
// claude
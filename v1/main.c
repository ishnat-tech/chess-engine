// Notes to self : 
// double \n might confuse uci so take care of that

// TODO
// 1.  DONE Print functions: single bitboard as 8x8 grid, and full board with piece letters
// 2.  DONE Decide extra board data: occupancy bitboards (white, black, all) and square-to-piece array
// 3.  DONE FEN parsing
// 4.  DONE Move representation: from, to, promotion, flags; plus text conversion (e2e4)
// 5.  DONE Attack generation: leapers (knight, king, pawn) via tables, then sliders (rook, bishop, queen)
// 6.  DONE "Is this square attacked?" function
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
// 16 bit integer used for moves
typedef uint16_t Move;

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

// bit manipulation macros inspired by (https://www.youtube.com/watch?v=A6Eu8xhwMkY)

// to check whether a square is occupied in a bitboard
#define get_bit(bitboard, index) ((bitboard) & (1ULL << (index)))  // Returns non-zero if the bit at 'index' is set in 'bitboard' (the AND with the single-1 mask overlaps), else 0 (the 1s fall on different squares).
// to set a square (turn the bit on) in a bitboard, in place
#define set_bit(bitboard, index) ((bitboard) |= (1ULL << (index)))  // Turns on the bit at 'index' directly in 'bitboard' (|= ORs in the single-1 mask, so that square becomes 1 and all other bits stay unchanged).
// to clear a square (turn the bit off) in a bitboard, in place (used different approach than video)
#define pop_bit(bitboard, index) ((bitboard) &= ~(1ULL << (index)))  // Clears the bit at 'index' in place: ~(1ULL << index) is a mask of all 1s with a single 0 at that square, so &= forces that bit to 0 and leaves the other 63 unchanged (safe even if the bit was already 0).

// packs from square, to square, and the code to one 16-bit integer
#define encode_move(from, to, code) ((Move) ((from) | ((to) << 6) | ((code) << 12)))
// gets the from square from the integer made by encode_move
#define get_from(encoded_move) ((encoded_move) & 0x3F)  // 0x3F = 0b111111
// gets the to square from the integer made by encode_move
#define get_to(encoded_move) (((encoded_move) >> 6) & (0x3F))
// gets the code from the integer made by encode_move
#define get_code(encoded_move) (((encoded_move) >> 12) & (0xF))  // since code is 4 bits we make the mask 0xF = 0b1111

// here move is the integer returned by the encode_move
#define is_capture(move)       ((get_code(move)) & 0x4)  // returns 4 for true and zero for false
#define is_promotion(move)     ((get_code(move)) & 0x8)  // returns 8 for true and zero for false
#define is_en_passant(move)    ((get_code(move)) == MOVE_EN_PASSANT)  // returns 1 for en_passant
#define is_double_push(move)   ((get_code(move)) == MOVE_DOUBLE_PUSH)  // returns 1 for double_push otherwise 0
#define is_castle(move)        (((get_code(move)) == MOVE_KING_CASTLE) || ((get_code(move)) == MOVE_QUEEN_CASTLE))  //  
#define promotion_piece(move)  ((get_code(move)) & 0x3)  // returns 0, 1, 2, 3 for knight, bishop, rook, queen respectively

// for the moves struct (the last 4 bits)
enum { MOVE_QUIET, MOVE_DOUBLE_PUSH, MOVE_KING_CASTLE, MOVE_QUEEN_CASTLE, MOVE_CAPTURE, MOVE_EN_PASSANT,
       MOVE_KNIGHT_PROMOTION = 8, MOVE_BISHOP_PROMOTION, MOVE_ROOK_PROMOTION, MOVE_QUEEN_PROMOTION,
       MOVE_KNIGHT_PROMOTION_CAPTURE, MOVE_BISHOP_PROMOTION_CAPTURE, MOVE_ROOK_PROMOTION_CAPTURE, MOVE_QUEEN_PROMOTION_CAPTURE };

// index will be used in set_start_position
// piece order matters: must match the letters string "PNBRQKpnbrqk" used when printing
enum { WHITE_PAWN, WHITE_KNIGHT, WHITE_BISHOP, WHITE_ROOK, WHITE_QUEEN, WHITE_KING,
       BLACK_PAWN, BLACK_KNIGHT, BLACK_BISHOP, BLACK_ROOK, BLACK_QUEEN, BLACK_KING,
       PIECE_COUNT };

// occupancies
enum { WHITE_OCC, BLACK_OCC, BOTH_OCC, OCC_COUNT };

// castling rights
enum { WHITE_KING_SIDE = 8, WHITE_QUEEN_SIDE = 4, BLACK_KING_SIDE = 2, BLACK_QUEEN_SIDE = 1 };

enum { WHITE_SIDE, BLACK_SIDE };

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

// FILE MASKS: used to stop shifted bits from wrapping around the board edge.
// bitboards for ensuring wrap around in a and h files

const U64 not_a_file  = 0xFEFEFEFEFEFEFEFEULL;  // a-file cleared
const U64 not_h_file  = 0x7F7F7F7F7F7F7F7FULL;  // h-file cleared
const U64 not_ab_file = 0xFCFCFCFCFCFCFCFCULL;  // a and b files cleared (knight)
const U64 not_gh_file = 0x3F3F3F3F3F3F3F3FULL;  // g and h files cleared (knight)

// if the shift moves the piece towards h-file, the danger is wrapping onto a-file, so AND with not_a_file
// if the shift moves the piece towards a-file, the danger is wrapping onto h-file, so AND with not_h_file
// knights jump two files sideways in some moves, so those use the two-file masks (not_ab_file / not_gh_file)
// shifts that only move up or down need no mask, since bits fall off the ends of the number, therefore no change is required

// << 1 : toward h-file          >> 1 : toward a-file
// << 9 : up and toward h-file   >> 9 : down and toward a-file
// << 7 : up and toward a-file   >> 7 : down and toward h-file
// << 8 : straight up            >> 8 : straight down


// rooks, bishops and queens do not have a table because they depend on the position
// array of bitboards

// king attacks table
U64 king_attacks[64];

// knight attacks table
U64 knight_attacks[64];

// pawn attacks table
// indexed by side first then squares
U64 pawn_attacks[2][64];

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

// function takes in a square and outputs a bitboard representing attacked squares for king
U64 compute_king_attacks(int square)
{ 
    U64 attack_bitboard = 0ULL;  // initialization
    U64 piece_bitboard = 0ULL;   // initialization

    set_bit(piece_bitboard, square);  // setting the bit at the square to 1
    
    // straight up or down, bits fall of the end therefore no masking
    attack_bitboard |= (piece_bitboard << 8);  // up
    attack_bitboard |= (piece_bitboard >> 8);  // down

    // moving towards h file
    attack_bitboard |= ((piece_bitboard << 9) & not_a_file);  // up and right
    attack_bitboard |= ((piece_bitboard << 1) & not_a_file);  // right
    attack_bitboard |= ((piece_bitboard >> 7) & not_a_file);  // down and right

    // moving towards a file
    attack_bitboard |= ((piece_bitboard << 7) & not_h_file);  // up and left
    attack_bitboard |= ((piece_bitboard >> 1) & not_h_file);  // left
    attack_bitboard |= ((piece_bitboard >> 9) & not_h_file);  // down and left

    return attack_bitboard;
}

// function takes in a square and outputs a bitboard representing attacked squares for knight
U64 compute_knight_attacks(int square)
{
    U64 attack_bitboard = 0ULL;  // initialization
    U64 piece_bitboard = 0ULL;   // initialization

    set_bit(piece_bitboard, square);  // setting the bit at the square to 1

    // jumps toward the h-file
    attack_bitboard |= ((piece_bitboard << 17) & not_a_file);   // up 2, right 1
    attack_bitboard |= ((piece_bitboard << 10) & not_ab_file);  // up 1, right 2
    attack_bitboard |= ((piece_bitboard >> 6)  & not_ab_file);  // down 1, right 2
    attack_bitboard |= ((piece_bitboard >> 15) & not_a_file);   // down 2, right 1

    // jumps toward the a-file
    attack_bitboard |= ((piece_bitboard << 15) & not_h_file);   // up 2, left 1
    attack_bitboard |= ((piece_bitboard << 6)  & not_gh_file);  // up 1, left 2
    attack_bitboard |= ((piece_bitboard >> 10) & not_gh_file);  // down 1, left 2
    attack_bitboard |= ((piece_bitboard >> 17) & not_h_file);   // down 2, left 1

    return attack_bitboard;
}

// function takes in a square and the color of the pawn and outputs a bitboard representing attack squares for pawn
// these are capture diagonals, pushes are handled in move generations
U64 compute_pawn_attacks(int side, int square)
{
    // side takes 0 and 1 for white and black respectively, using enum

    U64 attack_bitboard = 0ULL;  // initialization
    U64 piece_bitboard = 0ULL;   // initialization

    set_bit(piece_bitboard, square);  // setting the bit at  the square to 1

    if (side == WHITE_SIDE)
    {
        attack_bitboard |= ((piece_bitboard << 9) & not_a_file);  // up and right
        attack_bitboard |= ((piece_bitboard << 7) & not_h_file);  // up and left
    }
    else
    {
        attack_bitboard |= ((piece_bitboard >> 9) & not_h_file);  // down and left
        attack_bitboard |= ((piece_bitboard >> 7) & not_a_file);  // down and right
    }

    return attack_bitboard;
}

// initializes attack table for leaper piece types
void init_leaper_attack(void)
{
    for (int square = 0; square < 64; square++)
    {
        king_attacks[square] = compute_king_attacks(square);
        knight_attacks[square] = compute_knight_attacks(square);
        pawn_attacks[WHITE_SIDE][square] = compute_pawn_attacks(WHITE_SIDE, square);
        pawn_attacks[BLACK_SIDE][square] = compute_pawn_attacks(BLACK_SIDE, square);
    }
}

// function takes in a square and the bitboard (BOTH_OCCUPANCY) and outputs bitboard representing attacking square for rook
U64 compute_rook_attacks(int square, U64 occupancy)
{
    U64 attack_bitboard = 0ULL;  // initialization

    // since square = (rank * 8) + file
    int rank = square / 8;
    int file = square % 8;

    // up
    for (int r = rank + 1; r <= 7; r++)
    {
        int target = r * 8 + file;
        set_bit(attack_bitboard, target);  // first the bit is set then loop breaks so that we don't lose the attacked square
        if (get_bit(occupancy, target)) break;
    }

    // down
    for (int r = rank - 1; r >= 0; r--)
    {
        int target = r * 8 + file;
        set_bit(attack_bitboard, target);
        if (get_bit(occupancy, target)) break;
    }

    // right (toward h-file)
    for (int f = file + 1; f <= 7; f++)
    {
        int target = rank * 8 + f;
        set_bit(attack_bitboard, target);
        if (get_bit(occupancy, target)) break;
    }

    // left (toward a-file)
    for (int f = file - 1; f >= 0; f--)
    {
        int target = rank * 8 + f;
        set_bit(attack_bitboard, target);
        if (get_bit(occupancy, target)) break;
    }    

    return attack_bitboard;
}

// function takes in a square and the bitboard (BOTH_OCCUPANCY) and outputs bitboard representing attacking square for bishop
U64 compute_bishop_attacks(int square, U64 occupancy)
{
    U64 attack_bitboard = 0ULL;

    int rank = square / 8;  // 0-based rank
    int file = square % 8;  // 0-based file

    // up and right
    for (int r = rank + 1, f = file + 1; r <= 7 && f <= 7; r++, f++)
    {
        int target = r * 8 + f;
        set_bit(attack_bitboard, target);  // first the bit is set then loop breaks so that we don't lose the attacked square
        if (get_bit(occupancy, target)) break;
    }

    // up and left
    for (int r = rank + 1, f = file - 1; r <= 7 && f >= 0; r++, f--)
    {
        int target = r * 8 + f;
        set_bit(attack_bitboard, target);
        if (get_bit(occupancy, target)) break;
    }

    // down and right
    for (int r = rank - 1, f = file + 1; r >= 0 && f <= 7; r--, f++)
    {
        int target = r * 8 + f;
        set_bit(attack_bitboard, target);
        if (get_bit(occupancy, target)) break;
    }

    // down and left
    for (int r = rank - 1, f = file - 1; r >= 0 && f >= 0; r--, f--)
    {
        int target = r * 8 + f;
        set_bit(attack_bitboard, target);
        if (get_bit(occupancy, target)) break;
    }

    return attack_bitboard;
}

// queen = rook rays + bishop rays
U64 compute_queen_attacks(int square, U64 occupancy)
{
    return compute_rook_attacks(square, occupancy) | compute_bishop_attacks(square, occupancy);
}

// checks if a square is attacked
bool is_square_attacked(const Board *pos, int square, int attacker)
{
    // board is const because this function doesn't change the board
    
    // returns true if any piece of side 'attacker' attacks 'square'
    // works by looking outward from the target square: if a piece of each type standing on 'square'
    // would hit a real attacker of that type, then that attacker hits 'square'
    // relies on the piece enum layout: white pieces are 0-5 and black pieces are 6-11,
    // so (attacker * 6) is the offset to the attacker's pieces

    int offset = attacker * 6;  // 0 for white attacker, 6 for black attacker, to match the piece enum

    // pawns: pawn attacks are not symmetric, so use the OPPOSITE side's pawn table
    // (squares an opposing pawn on 'square' would hit = squares where an attacking pawn would have to stand)
    if (pawn_attacks[1 - attacker][square] & pos->bitboards[WHITE_PAWN + offset]) return true;

    // knights: knight attacks are symmetric, so squares a knight on 'square' could reach
    // that hold an attacker's knight mean the square is attacked
    if (knight_attacks[square] & pos->bitboards[WHITE_KNIGHT + offset]) return true;

    // king: same idea as knights, using the king table and the attacker's king
    if (king_attacks[square] & pos->bitboards[WHITE_KING + offset]) return true;

    // bishops and queens: diagonal rays from 'square', stopped by any piece (BOTH_OCC),
    // that reach an attacker's bishop or queen
    if (compute_bishop_attacks(square, pos->occupancies[BOTH_OCC]) &
        (pos->bitboards[WHITE_BISHOP + offset] | pos->bitboards[WHITE_QUEEN + offset])) return true;

    // rooks and queens: straight rays from 'square', stopped by any piece (BOTH_OCC),
    // that reach an attacker's rook or queen
    if (compute_rook_attacks(square, pos->occupancies[BOTH_OCC]) &
        (pos->bitboards[WHITE_ROOK + offset] | pos->bitboards[WHITE_QUEEN + offset])) return true;

    // no check found an attacker, so the square is not attacked
    return false;
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

    int rank = 8, file = 0;  // for file, 0 represents a file, 1 b file, ...

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
        else if (isdigit((unsigned char)(fen[i])))
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
        while (isdigit((unsigned char)fen[i])) i++;

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
        // prints rank number
        printf("%d ", rank);

        for (int file = 0; file < 8; file++)
        {
            int square = (rank - 1) * 8 + file;
            printf(" %d", get_bit(bitboard, square) ? 1 : 0);
        }
        printf("\n");
    }
    printf("\n   a b c d e f g h\n");  // prints file letter
    printf("\nhex: 0x%016llX\n\n", (unsigned long long)bitboard);  // prints bitboard as 16-digit zero-padded uppercase hex
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
void print_move(Move move)
{
    printf("%s%s", square_names[get_from(move)], square_names[get_to(move)]);

    if (is_promotion(move))
    {
        switch (promotion_piece(move))
        {
            case 0: printf("n"); break;
            case 1: printf("b"); break;
            case 2: printf("r"); break;
            case 3: printf("q"); break;
        }
    }

    printf("\n\n");
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
    // Move move = 5900;  // rn hardcoded e2 to e4 for testing
    // print_moves(move);
    init_leaper_attack();
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
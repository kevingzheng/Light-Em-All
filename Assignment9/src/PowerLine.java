
/* Extra Credit Added:
Whistles
1. Implemented gradient coloring.
2. Allows the user to start a new problem without restarting the problem
   (Note: the user has to win the game to start a new program, 
          but there is a show solution feature if they dont want to solve it)
3. Keeping Score. Renders the number of moves used in real time. 
4. Keeping time. Renders the time taken so far in the game

Bells:
1. Construct wiring with a bias in a particular direction — 
   a preference for horizontal or vertical wires
   (Note: The constructor for the game takes in a bias that is an int. 
          If the int is positive, the bias is towards vertical wires.
          If the int is negative, the bias is towards horizontal wires. 
          If the int is 0, then there is no bias. 

Other Features Implemented:
1. Winning scene / Losing scene implemented:
                  Allows the user to interact with the game.
                  Essentially gives them the ability to move between different views of the game. 
                  Winning Scene:
                      Allows user to enter their name, press space to play again, 
                      or press escape to quit the game altogether. 
                  
                  Losing Scene: 
                     Allows user to replay the game by pressing shift. 
                     Allows user to press escape to quit the game altogether. 
2. Show Solution: Button that the user can click to have the correct solution shown to them. 
                  The user will still need to move the power station to the center of the board. 
3. Reset Game: The user is able to reset the board 
               so that they can start over with the original board given.    
4. Maximum number of moves allowed: 
           The game will give the user a set amount of moves they have to win the game.
           If they are unable to complete the game in those moves, they lose. 
           If they lose, they have the option to replay that puzzle. 
5. Entering your name:
           If the user wins the game, they have the ability to write their name. 
           Names must be lowercase and cannot contain special characters
           (eg. shift, space, slash, hyphen). 
6. Writing winning entries to a csv file:
           Once the user wins and enters their name, 
           they can press enter to save their name/stats to a csv file, called leaderboard.csv
           
           If the csv file(leaderboard.csv) already exists, it writes the entry to that file.

           Otherwise, it creates a new csv file. 
           
           The file has the following columns: 
           Name, Rows, Columns, Number of Moves Needed, Looked at Solution(t/f).

           The game can be played multiple times and have multiple entries be added to the file.
           
           If the game is quit and then restarted, 
           additional entries will still be appended to the already created file. 
           
           Note: The user will have to actually end the game(press escape) 
           to write their entry in the file.
           
           To see the leaderboard, you will need to download this file 
           and ideally place it in the desktop. 
           There will be a file created then called leaderboard.csv. 
           
           Note: Writing tests using checkExpects for leaderboard is virtually impossible 
           However, it can easily be seen that the leaderboard file works 
           simply by opening the file upon the completion of the game. 
*/

import java.awt.Color;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Random;

import javalib.impworld.*;
import javalib.worldimages.*;
import tester.*;

// class that represents the Game
class LightEmAll extends World {

  // a list of columns of GamePieces,
  // i.e., represents the board in column-major order
  ArrayList<ArrayList<GamePiece>> board;
  // a list of edges of the minimum spanning tree
  ArrayList<Edge> mst;
  // the width and height of the board
  int width;
  int height;
  // represents the number of tiles in on the board
  int numTilesWidth;
  int numTilesHeight;
  // the current location of the power station,
  // as well as its effective radius
  int powerRow;
  int powerCol;
  // the radius of the board
  int radius;
  // represents the tile size
  int tileSize;
  // represents the time taken
  int timer;
  // represents the number of moves the user has made so far
  int moves;
  // represents the minimum number of moves needed to solve the game.
  int numMovesNeeded;
  // represents the initial board that is created.
  ArrayList<ArrayList<GamePiece>> currState = new ArrayList<ArrayList<GamePiece>>();
  // represents the name of the user plaing the game
  String name;
  // represents whether or not the game is over
  boolean gameOver;
  // the output that will be written to the file
  BufferedWriter output = null;
  // represents whether the user has looked at the solution
  boolean lookedAtSolution;
  // represents the bias, should be given as an int between -3 and 3
  int bias;
  // field for testing randoms
  Random random;

  // constructor for the game
  LightEmAll(int width, int height, int numTilesWidth, int numTilesHeight, int bias) {
    this.random = new Random();
    // initializes the fields to the given parameters
    this.numTilesWidth = numTilesWidth;
    this.numTilesHeight = numTilesHeight;
    this.width = width;
    this.height = height;
    this.bias = bias;
    // sets the power row and power col to be in the upper middle of the board.
    this.powerCol = this.numTilesWidth / 2;
    this.powerRow = 0;
    // initailizes the board to an empty arraylist of arraylist of gamepiece
    this.board = new ArrayList<ArrayList<GamePiece>>();
    // sets the tile size
    this.tileSize = Math.min((int) (.9 * width / numTilesWidth),
        (int) (.9 * height / numTilesHeight));
    // sets the board using kruskals algorithm
    this.board = createBoard();
    this.mst = kruskalAlgos();
    this.createBoardWithMst();
    // removes and then adds all the neighbors for each gamepiece
    this.removeNeighbors();
    this.addNeighbors();
    // turns every gamepiece off
    this.turnGamePieceOff();
    // sets the radius
    this.radius = getRadius();
    this.name = "";
    this.timer = 0;
    this.moves = 0;
    // lights the cells based on the radius
    this.board.get(this.powerCol).get(this.powerRow).lightCells(this.radius + 1);
    this.gameOver = false;
    // gets the minimum number of moves needed to win the game and rotates the
    // gamepieces
    this.numMovesNeeded = rotations();
    // saves the current state to allow for resets
    saveCurrState();
    this.lookedAtSolution = false;

    // writes the header("name", "columns", "rows,", "number of moves", "looked at
    // solution") to a csv file called leaderboard
    try {
      this.output = new BufferedWriter(new FileWriter("leaderboard.csv", true));
      StringBuilder sb = new StringBuilder();
      sb.append("Name");
      sb.append(',');
      sb.append("Columns");
      sb.append(',');
      sb.append("Rows");
      sb.append(',');
      sb.append("Number Of Moves");
      sb.append(',');
      sb.append("Looked at Solution");
      sb.append('\n');
      this.output.write(sb.toString());
    } catch (IOException e) {
      e.printStackTrace();
    }

  }

  LightEmAll(int width, int height, int numTilesWidth, int numTilesHeight, int bias,
      Random random) {
    this.random = random;
    // initializes the fields to the given parameters
    this.numTilesWidth = numTilesWidth;
    this.numTilesHeight = numTilesHeight;
    this.width = width;
    this.height = height;
    this.bias = bias;
    // sets the power row and power col to be in the upper middle of the board.
    this.powerCol = this.numTilesWidth / 2;
    this.powerRow = 0;
    // initailizes the board to an empty arraylist of arraylist of gamepiece
    this.board = new ArrayList<ArrayList<GamePiece>>();
    // sets the tile size
    this.tileSize = Math.min((int) (.9 * width / numTilesWidth),
        (int) (.9 * height / numTilesHeight));
    // sets the board using kruskals algorithm
    this.board = createBoard();
    this.mst = kruskalAlgos();
    this.createBoardWithMst();
    // removes and then adds all the neighbors for each gamepiece
    this.removeNeighbors();
    this.addNeighbors();
    // turns every gamepiece off
    this.turnGamePieceOff();
    // sets the radius
    this.radius = getRadius();
    this.name = "";
    this.timer = 0;
    this.moves = 0;
    // lights the cells based on the radius
    this.board.get(this.powerCol).get(this.powerRow).lightCells(this.radius + 1);
    this.gameOver = false;
    // gets the minimum number of moves needed to win the game and rotates the
    // gamepieces
    this.numMovesNeeded = rotations();
    // saves the current state to allow for resets
    saveCurrState();
    this.lookedAtSolution = false;

    // writes the header("name", "columns", "rows,", "number of moves", "looked at
    // solution") to a csv file called leaderboard
    try {
      this.output = new BufferedWriter(new FileWriter("leaderboard.csv", true));
      StringBuilder sb = new StringBuilder();
      sb.append("Name");
      sb.append(',');
      sb.append("Columns");
      sb.append(',');
      sb.append("Rows");
      sb.append(',');
      sb.append("Number Of Moves");
      sb.append(',');
      sb.append("Looked at Solution");
      sb.append('\n');
      this.output.write(sb.toString());
    } catch (IOException e) {
      e.printStackTrace();
    }

  }

  // saves the current state of the board to a duplicate
  void saveCurrState() {
    for (int i = 0; i < this.board.size(); i++) {
      ArrayList<GamePiece> temp = new ArrayList<GamePiece>();
      for (int j = 0; j < this.board.get(i).size(); j++) {
        GamePiece curr = this.board.get(i).get(j);
        int currRow = curr.row;
        int currCol = curr.col;
        boolean left = curr.left;
        boolean right = curr.right;
        boolean bottom = curr.bottom;
        boolean top = curr.top;
        boolean powerStation = curr.powerStation;
        int wireSize = curr.wireSize;
        GamePiece current = new GamePiece(currRow, currCol, left, right, top, bottom, powerStation,
            wireSize);
        temp.add(current);
      }
      this.currState.add(temp);
    }
  }

  // creates the grid
  ArrayList<ArrayList<GamePiece>> createBoard() {
    ArrayList<ArrayList<GamePiece>> temp = new ArrayList<ArrayList<GamePiece>>();
    for (int i = 0; i < numTilesWidth; i++) {
      ArrayList<GamePiece> mt = new ArrayList<GamePiece>();
      for (int j = 0; j < numTilesHeight; j++) {
        if (i == powerCol && j == powerRow) {

          GamePiece riggedGP = new GamePiece(i, j, false, false, false, false, true, tileSize / 2);
          mt.add(riggedGP);
        } else {
          GamePiece newGP = new GamePiece(i, j, false, false, false, false, false, tileSize / 2);
          mt.add(newGP);
        }
      }
      temp.add(mt);
    }
    return temp;
  }

  // rotates the gamepiece edges and returns the number of rotations that occur
  int rotations() {
    int moves = 0;
    for (int i = 0; i < this.board.size(); i++) {
      for (int j = 0; j < this.board.get(i).size(); j++) {
        int rotations = this.random.nextInt(4);
        moves = moves + 4 - rotations;
        while (rotations > 0) {
          this.board.get(i).get(j).rotate();
          rotations--;
        }

      }

    }
    this.removeNeighbors();
    this.addNeighbors();
    this.turnGamePieceOff();
    this.board.get(this.powerCol).get(this.powerRow).lightCells(this.radius + 1);
    return moves + this.radius;
  }

  // draws the gamepieces of the board.
  WorldImage drawTiles() {
    WorldImage temp = new EmptyImage();
    for (int i = 0; i < this.board.size(); i++) {
      WorldImage innerTemp = new EmptyImage();
      for (int j = 0; j < this.board.get(i).size(); j++) {
        innerTemp = new AboveImage(innerTemp, this.board.get(i).get(j).draw(this.tileSize));
      }
      temp = new BesideImage(temp, innerTemp);
    }
    return temp;
  }

  // returns the time text based on the time elapsed
  String getTimeText() {
    String timeText = "";
    // checks to see if minutes are needed.
    if (this.timer < 60) {
      if (this.timer % 60 != 1) {
        timeText = "Time: " + this.timer + " seconds";
      } else {
        timeText = "Time: " + this.timer + " second";
      }

    } else {
      if (this.timer % 60 != 1) {
        if ((int) (this.timer / 60) == 1) {
          timeText = "Time: " + (int) (this.timer / 60) + " minute " + this.timer % 60 + " seconds";
        } else {
          timeText = "Time: " + (int) (this.timer / 60) + " minutes " + this.timer % 60
              + " seconds";
        }
      } else {
        if ((int) (this.timer / 60) == 1) {
          timeText = "Time: " + (int) (this.timer / 60) + " minute " + this.timer % 60 + " second";
        } else {
          timeText = "Time: " + (int) (this.timer / 60) + " minutes " + this.timer % 60 + " second";
        }
      }

    }
    return timeText;
  }

  // renders the World Scene
  public WorldScene makeScene() {
    WorldScene scene = new WorldScene(width, height);

    scene.placeImageXY(drawTiles(), width / 2, height / 2);
    TextImage timeCount = new TextImage(getTimeText(), Color.BLACK);
    TextImage movesCount = new TextImage("Number of Moves: " + this.moves, Color.BLACK);
    TextImage movesNeeded = new TextImage("Number of Moves Needed: " + this.numMovesNeeded,
        Color.BLACK);
    TextImage resetText = new TextImage("Press shift to Reset", Color.BLACK);
    WorldImage resetButton = new RectangleImage(this.width / 4, this.height / 20,
        OutlineMode.OUTLINE, Color.BLUE);
    int userMovesRemaining = 3 * this.numMovesNeeded / 2 + this.radius - this.moves;
    TextImage userMovesNeeded = new TextImage("Number of Moves Left: " + userMovesRemaining,
        Color.BLACK);
    TextImage showSolution = new TextImage("Show Solution", Color.BLACK);
    WorldImage solutionButton = new RectangleImage(this.width / 4, this.height / 20,
        OutlineMode.OUTLINE, Color.RED);
    scene.placeImageXY(resetText, (int) (this.width / 2), (int) (.025 * this.height));
    scene.placeImageXY(resetButton, (int) (this.width / 2), (int) (.025 * this.height));
    scene.placeImageXY(timeCount, (int) (this.width / 7), (int) (.98 * this.height));
    scene.placeImageXY(movesCount, (int) (this.width / 2), (int) (.98 * this.height));
    scene.placeImageXY(movesNeeded, (int) (5 * this.width / 6), (int) (.98 * this.height));
    scene.placeImageXY(userMovesNeeded, this.width / 6, (int) (.025 * this.height));
    scene.placeImageXY(showSolution, (int) (4 * this.width / 5), (int) (.025 * this.height));
    scene.placeImageXY(solutionButton, (int) (4 * this.width / 5), (int) (.025 * this.height));
    if (3 * this.numMovesNeeded / 2 + this.radius - this.moves < 0) {
      return loser();
    }
    if (this.isWinner()) {
      return winner();
    }
    return scene;
  }

  // returns the worldscene if the game has been won.
  WorldScene winner() {
    WorldScene scene = new WorldScene(this.width, this.height);
    TextImage winnerText = new TextImage("You Won!", Color.GREEN);
    TextImage newGameText = new TextImage("Press space to Play Again", Color.BLACK);
    TextImage endGame = new TextImage("Press escape to exit", Color.BLACK);
    TextImage name = new TextImage("Enter Your Name: " + this.name, Color.BLACK);
    WorldImage newGameButton = new RectangleImage(3 * this.width / 10, this.height / 20,
        OutlineMode.SOLID, Color.GREEN);
    scene.placeImageXY(endGame, this.width / 2, 11 * this.height / 20);
    scene.placeImageXY(winnerText, this.width / 2, 2 * this.height / 5);
    scene.placeImageXY(name, this.width / 2, this.width / 2);
    scene.placeImageXY(newGameButton, this.width / 2, 3 * this.height / 5);
    scene.placeImageXY(newGameText, this.width / 2, 3 * this.height / 5);
    return scene;
  }

  // returns the worldscene if the game has been lost
  WorldScene loser() {
    WorldScene scene = new WorldScene(this.width, this.height);
    TextImage loserText = new TextImage("You Lost!", Color.RED);
    TextImage newGameText = new TextImage("Press shift to play again", Color.BLACK);
    WorldImage newGameButton = new RectangleImage(3 * this.width / 10, this.height / 20,
        OutlineMode.SOLID, Color.RED);
    TextImage endGame = new TextImage("Press escape to exit", Color.BLACK);
    scene.placeImageXY(loserText, this.width / 2, 2 * this.height / 5);
    scene.placeImageXY(endGame, this.width / 2, 9 * this.height / 20);

    scene.placeImageXY(newGameButton, this.width / 2, 3 * this.height / 5);
    scene.placeImageXY(newGameText, this.width / 2, 3 * this.height / 5);
    return scene;

  }

  // onTick method that increments the time every second
  public void onTick() {
    this.timer++;
  }

  // Rotates a game piece if it is left clicked on, otherwise does nothing
  public void onMouseClicked(Posn pos, String buttonName) {
    if (pos.x >= this.width / 2 - this.tileSize * this.numTilesWidth / 2
        && pos.x <= this.width / 2 + this.tileSize * this.numTilesWidth / 2
        && pos.y >= this.height / 2 - this.tileSize * this.numTilesHeight / 2
        && pos.y <= this.height / 2 + this.tileSize * this.numTilesHeight / 2 && !isWinner()) {

      int w = (pos.x - (this.width / 2 - this.tileSize * this.numTilesWidth / 2)) / this.tileSize;
      int h = (pos.y - (this.width / 2 - this.tileSize * this.numTilesHeight / 2)) / this.tileSize;
      if (buttonName.equals("LeftButton")) {
        GamePiece clicked = this.board.get(w).get(h);
        clicked.rotate();
      }
      this.moves++;
    }

    // wipe the cells
    turnGamePieceOff();
    this.removeNeighbors();
    this.addNeighbors();

    // if the show solution button is clicked
    this.board.get(powerCol).get(powerRow).lightCells(this.radius + 1);
    if (pos.x < (int) (.925 * this.width) && pos.x > (int) (.675 * this.width)
        && pos.y < (int) (.05 * this.height)) {
      showSolution();

    }

  }

  // shows the solution for the puzzle
  void showSolution() {
    this.board = this.createBoard();
    this.kruskalAlgos();
    this.createBoardWithMst();
    // this.createFractals(this.board);
    this.removeNeighbors();
    this.addNeighbors();
    this.board.get(this.powerCol).get(this.powerRow).powerStation = false;
    this.powerCol = this.numTilesWidth / 2;
    this.powerRow = 0;
    this.board.get(this.powerCol).get(this.powerRow).powerStation = true;
    turnGamePieceOff();
    this.board.get(this.powerCol).get(this.powerRow).lightCells(this.radius + 1);
    this.timer = 0;
    this.moves = 0;
    this.lookedAtSolution = true;
  }

  // resets the board to the original state
  void reset() {
    for (int i = 0; i < this.currState.size(); i++) {
      ArrayList<GamePiece> temp = new ArrayList<GamePiece>();
      for (int j = 0; j < this.currState.get(i).size(); j++) {
        GamePiece curr = this.currState.get(i).get(j);
        if (curr.powerStation) {
          this.powerCol = curr.row;
          this.powerRow = curr.col;
        }
        int currRow = curr.row;
        int currCol = curr.col;
        boolean left = curr.left;
        boolean right = curr.right;
        boolean bottom = curr.bottom;
        boolean top = curr.top;
        boolean powerStation = curr.powerStation;
        int wireSize = curr.wireSize;
        GamePiece current = new GamePiece(currRow, currCol, left, right, top, bottom, powerStation,
            wireSize);
        temp.add(current);
      }
      this.board.set(i, temp);
    }

    this.removeNeighbors();
    this.addNeighbors();
    this.turnGamePieceOff();
    this.timer = 0;
    this.moves = 0;
    this.board.get(this.powerCol).get(this.powerRow).lightCells(this.radius + 1);
    this.lookedAtSolution = false;

  }

  // creates a new puzzle board.
  void newGame() {
    this.powerCol = this.numTilesWidth / 2;
    this.powerRow = 0;
    this.board = createBoard();
    this.mst = kruskalAlgos();
    this.createBoardWithMst();
    this.removeNeighbors();
    this.addNeighbors();
    this.turnGamePieceOff();
    this.radius = getRadius();
    this.name = "";
    this.timer = 0;
    this.moves = 0;

    this.board.get(this.powerCol).get(this.powerRow).lightCells(this.radius + 1);

    this.numMovesNeeded = rotations();
    for (int i = 0; i < this.board.size(); i++) {
      ArrayList<GamePiece> temp = new ArrayList<GamePiece>();
      for (int j = 0; j < this.board.get(i).size(); j++) {
        GamePiece curr = this.board.get(i).get(j);
        int currRow = curr.row;
        int currCol = curr.col;
        boolean left = curr.left;
        boolean right = curr.right;
        boolean bottom = curr.bottom;
        boolean top = curr.top;
        boolean powerStation = curr.powerStation;
        int wireSize = curr.wireSize;
        GamePiece current = new GamePiece(currRow, currCol, left, right, top, bottom, powerStation,
            wireSize);
        temp.add(current);
      }
      this.currState.set(i, temp);
    }
    // sets looked at solution to false because the user no longer has the solution
    this.lookedAtSolution = false;
  }

  // sets the board using the minimum spanning tree that was generated
  void createBoardWithMst() {

    for (int i = 0; i < this.mst.size(); i++) {
      GamePiece curr1 = this.mst.get(i).fromNode;
      GamePiece curr2 = this.mst.get(i).toNode;

      if (curr1.row == curr2.row) {
        if (curr1.col == curr2.col + 1) {
          this.board.get(curr1.row).get(curr1.col).top = true;
          this.board.get(curr2.row).get(curr2.col).bottom = true;
        } else {
          this.board.get(curr1.row).get(curr1.col).bottom = true;
          this.board.get(curr2.row).get(curr2.col).top = true;
        }
      }
      if (curr1.col == curr2.col) {
        if (curr1.row == curr2.row + 1) {
          this.board.get(curr1.row).get(curr1.col).left = true;
          this.board.get(curr2.row).get(curr2.col).right = true;
        } else {
          this.board.get(curr1.row).get(curr1.col).right = true;
          this.board.get(curr1.row).get(curr2.col).left = true;
        }
      }
    }

  }

  // turns every game piece to be powered off
  void turnGamePieceOff() {
    for (int i = 0; i < this.board.size(); i++) {
      for (int j = 0; j < this.board.get(i).size(); j++) {
        this.board.get(i).get(j).powered = 0;
      }
    }
  }

  // checks to see if every gamepiece is lit up
  boolean isWinner() {
    for (int i = 0; i < this.board.size(); i++) {
      for (int j = 0; j < this.board.get(i).size(); j++) {
        if (this.board.get(i).get(j).powered == 0) {
          return false;
        }
      }
    }

    return true;
  }

  // sets the name to the string given by the onKeyEvent method
  void writeName(String key) {
    // creates an arraylist of "good keys" that can be used to enter in your name.
    ArrayList<String> goodKeys = new ArrayList<String>(
        Arrays.asList("a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o",
            "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z"));
    if (goodKeys.contains(key)) {
      this.name = this.name + key;
    }
    if (key.equals("backspace")) {
      String temp = this.name;
      if (temp.length() > 0) {
        this.name = temp.substring(0, temp.length() - 1);
      }
    }
  }

  // ends the world
  public WorldEnd worldEnds() {
    if (this.gameOver) {
      try {
        this.output.close();
      } catch (IOException e) {
        e.printStackTrace();
      }
      return new WorldEnd(true, this.makeAFinalScene());
    } else {
      return new WorldEnd(false, this.makeScene());
    }
  }

  // makes the final end world scene
  WorldScene makeAFinalScene() {
    WorldScene scene = new WorldScene(this.width, this.height);
    TextImage finalText = new TextImage("Game Over", Color.BLACK);
    scene.placeImageXY(finalText, this.width / 2, this.height / 2);
    return scene;

  }

  // onkey event
  public void onKeyEvent(String key) {
    // if the game has been won, writes the name that is currently being entered
    if (isWinner()) {
      writeName(key);
    }
    if (!isWinner() && key.equals("shift")) {
      reset();
      return;
    }
    if (key.equals(" ") && isWinner()) {
      newGame();
      return;
    }
    if (key.equals("escape")) {
      this.gameOver = true;
    }
    // appends the entry to the existing file
    if (key.equals("enter") && isWinner()) {
      String leaderName = this.name;
      this.name = "";

      try {
        StringBuilder sb = new StringBuilder();
        sb.append(leaderName);
        sb.append(',');
        sb.append(this.numTilesWidth);
        sb.append(',');
        sb.append(this.numTilesHeight);
        sb.append(',');
        sb.append(this.moves);
        sb.append(',');
        sb.append(this.lookedAtSolution);
        sb.append('\n');

        this.output.write(sb.toString());
      } catch (IOException e) {
        e.printStackTrace();
      }
      return;
    }

    if (!isWinner()) {
      if (key.equals("up") && this.powerRow > 0 && this.board.get(this.powerCol).get(this.powerRow)
          .isConnectedTop(this.board.get(this.powerCol).get(this.powerRow - 1))) {
        this.board.get(this.powerCol).get(this.powerRow).powerStation = false;
        this.powerRow--;
        this.board.get(this.powerCol).get(this.powerRow).powerStation = true;
      }
      if (key.equals("down") && this.powerRow < this.numTilesHeight - 1
          && this.board.get(this.powerCol).get(this.powerRow)
              .isConnectedBottom(this.board.get(this.powerCol).get(this.powerRow + 1))) {
        this.board.get(this.powerCol).get(this.powerRow).powerStation = false;
        this.powerRow++;
        this.board.get(this.powerCol).get(this.powerRow).powerStation = true;
      }
      if (key.equals("right") && this.powerCol < this.numTilesWidth - 1
          && this.board.get(this.powerCol).get(this.powerRow)
              .isConnectedRight(this.board.get(this.powerCol + 1).get(this.powerRow))) {
        this.board.get(this.powerCol).get(this.powerRow).powerStation = false;
        this.powerCol++;
        this.board.get(this.powerCol).get(this.powerRow).powerStation = true;

      }
      if (key.equals("left") && this.powerCol > 0 && this.board.get(powerCol).get(powerRow)
          .isConnectedLeft(this.board.get(powerCol - 1).get(powerRow))) {
        this.board.get(this.powerCol).get(this.powerRow).powerStation = false;
        this.powerCol--;
        this.board.get(this.powerCol).get(this.powerRow).powerStation = true;
      }
      // wipe the cells
      turnGamePieceOff();
      this.board.get(powerCol).get(powerRow).lightCells(this.radius + 1);
      this.moves++;
    }

  }

  // goes through every gamepiece and removes their neighbors.
  void removeNeighbors() {
    for (int i = 0; i < this.board.size(); i++) {
      for (int j = 0; j < this.board.get(i).size(); j++) {
        GamePiece curr = this.board.get(i).get(j);
        curr.neighbors = new ArrayList<GamePiece>();
      }
    }
  }

  // goes through every gamepiece and adds their corresponding neighbors.
  void addNeighbors() {
    for (int i = 0; i < this.board.size(); i++) {
      for (int j = 0; j < this.board.get(i).size(); j++) {
        GamePiece curr = this.board.get(i).get(j);
        if (i > 0) {
          if (curr.isConnectedLeft(this.board.get(i - 1).get(j))) {
            curr.addNeighbor(this.board.get(i - 1).get(j));
          }
        }
        if (j > 0) {
          if (curr.isConnectedTop(this.board.get(i).get(j - 1))) {
            curr.addNeighbor(this.board.get(i).get(j - 1));
          }
        }
        if (i < this.board.size() - 1) {
          if (curr.isConnectedRight(this.board.get(i + 1).get(j))) {
            curr.addNeighbor(this.board.get(i + 1).get(j));
          }
        }
        if (j < this.board.get(i).size() - 1) {
          if (curr.isConnectedBottom(this.board.get(i).get(j + 1))) {
            curr.addNeighbor(this.board.get(i).get(j + 1));
          }
        }
      }
    }
  }

  // gets the radius of the board.
  int getRadius() {
    GamePieceDepth furthestFirst = bfs(new Posn(this.powerCol, this.powerRow));
    GamePieceDepth furthestSecond = bfs(furthestFirst.getCoordinates());

    return furthestSecond.depth / 2 + 1;

  }

  // returns a gamepiece depth after executing a breadth first search given a
  // position in the board.
  GamePieceDepth bfs(Posn coord) {
    GamePiece curr = this.board.get(coord.x).get(coord.y);
    ArrayList<GamePieceDepth> sofar = new ArrayList<GamePieceDepth>();
    Queue<GamePieceDepth> queue = new LinkedList<GamePieceDepth>();
    queue.add(new GamePieceDepth(curr, 0));
    GamePieceDepth removed = null;
    while (!queue.isEmpty()) {
      removed = queue.remove();
      for (GamePiece gamePiece : removed.gp.neighbors) {
        if (!gamePiece.gamePieceInDepth(sofar)) {
          sofar.add(removed);
          queue.add(new GamePieceDepth(gamePiece, removed.depth + 1));
        }
      }
    }
    return removed;
  }

  // implements union find that efficiently connects components. returns an
  // arraylist of edges.
  ArrayList<Edge> kruskalAlgos() {
    HashMap<GamePiece, GamePiece> representatives = new HashMap<GamePiece, GamePiece>();

    for (int i = 0; i < this.board.size(); i++) {
      for (int j = 0; j < this.board.get(i).size(); j++) {
        GamePiece curr = this.board.get(i).get(j);
        representatives.put(curr, curr);
      }
    }

    ArrayList<Edge> edgesInTree = new ArrayList<Edge>();
    EdgeComp comp = new EdgeComp();
    ArrayList<Edge> worklist = this.generateEdges();
    worklist.sort(comp);

    while (worklist.size() > 0) {
      Edge current = worklist.get(0);
      if (representatives.get(current.fromNode).equals(representatives.get(current.toNode))) {
        worklist.remove(current);
      } else {
        edgesInTree.add(worklist.remove(0));
        union(representatives, representatives.get(current.fromNode),
            representatives.get(current.toNode));
      }
    }
    return edgesInTree;

  }

  // union method that sets one representatives representatives to the other.
  void union(HashMap<GamePiece, GamePiece> representatives, GamePiece x, GamePiece y) {
    ArrayList<GamePiece> groupX = findGroupOfGamePiece(representatives, x);
    ArrayList<GamePiece> groupY = findGroupOfGamePiece(representatives, y);

    if (groupX.size() < groupY.size()) {
      representatives = changeValues(representatives, x, y);
    } else {
      representatives = changeValues(representatives, y, x);
    }
  }

  // changes the values to set one representative to the other.
  HashMap<GamePiece, GamePiece> changeValues(HashMap<GamePiece, GamePiece> representatives,
      GamePiece x, GamePiece y) {
    ArrayList<GamePiece> xGroup = findGroupOfGamePiece(representatives, x);
    for (int i = 0; i < xGroup.size(); i++) {
      representatives.remove(xGroup.get(i));
      representatives.put(xGroup.get(i), y);
    }
    return representatives;
  }

  // finds what in a gamepiece group and returns an arraylist of gamepiece that
  // are in the group.
  ArrayList<GamePiece> findGroupOfGamePiece(HashMap<GamePiece, GamePiece> representatives,
      GamePiece x) {

    ArrayList<GamePiece> gpInGroup = new ArrayList<GamePiece>();
    for (int i = 0; i < this.board.size(); i++) {
      for (int j = 0; j < this.board.get(i).size(); j++) {
        GamePiece curr = this.board.get(i).get(j);
        if (representatives.get(curr) != null && representatives.get(curr).equals(x)) {
          gpInGroup.add(curr);
        }
      }
    }
    return gpInGroup;

  }

  // returns an arraylist of edges. Generating an edge for each gamepiece.
  ArrayList<Edge> generateEdges() {
    ArrayList<Edge> listOfEdges = new ArrayList<Edge>();
    int totalNumWeights = this.numTilesHeight * this.numTilesWidth - 1;
    int biasVert = 1;
    int biasHor = 1;
    if (this.bias > 0) {
      biasVert = this.bias;
    } else if (this.bias < 0) {
      biasHor = this.bias * -1;
    }
    for (int i = 0; i < this.board.size(); i++) {
      for (int j = 0; j < this.board.get(i).size(); j++) {
        GamePiece curr = this.board.get(i).get(j);
        if (i > 0) {
          Edge newEdge = new Edge(curr, this.board.get(i - 1).get(j),
              random.nextInt(totalNumWeights) * biasVert);
          listOfEdges.add(newEdge);
        }
        if (j > 0) {
          Edge newEdge = new Edge(curr, this.board.get(i).get(j - 1),
              random.nextInt(totalNumWeights) * biasHor);
          listOfEdges.add(newEdge);
        }

      }
    }

    return listOfEdges;
  }

}

// class EdgeComp that implements a comparator. 
class EdgeComp implements Comparator<Edge> {

  // compare method that compares two edge weights and returns - if the first
  // weight is greater, 0 if equal and + if the second is greater
  public int compare(Edge e, Edge other) {
    return e.weight - other.weight;
  }

}

// Class GamePieceDepth that has a gamepiece and depth.
class GamePieceDepth {
  GamePiece gp;
  int depth;

  // constructor for gamepiecedepth
  GamePieceDepth(GamePiece gp, int depth) {
    this.gp = gp;
    this.depth = depth;
  }

  // gets the coordinates of the gamepiece. Returns the row and col.
  Posn getCoordinates() {
    return new Posn(this.gp.row, this.gp.col);
  }

}

// class that represents a game piece
class GamePiece {
  // in logical coordinates, with the origin
  // at the top-left corner of the screen
  // rows and cols start at 0
  int row;
  int col;
  // whether this GamePiece is connected to the
  // adjacent left, right, top, or bottom pieces
  boolean left;
  boolean right;
  boolean top;
  boolean bottom;
  // whether the power station is on this piece
  boolean powerStation;
  int wireSize;
  int powered;
  ArrayList<GamePiece> neighbors;

  // constructor for GamePiece
  GamePiece(int row, int col, boolean left, boolean right, boolean top, boolean bottom,
      boolean powerStation, int wireSize) {
    this.row = row;
    this.col = col;
    this.left = left;
    this.right = right;
    this.top = top;
    this.bottom = bottom;
    this.powerStation = powerStation;
    this.wireSize = wireSize;
    this.powered = 0;
    this.neighbors = new ArrayList<GamePiece>();
  }

  // returns whether or not this gamepiece is in the given list of gamepiece
  // depth.
  boolean gamePieceInDepth(ArrayList<GamePieceDepth> gpd) {
    for (int i = 0; i < gpd.size(); i++) {
      if (gpd.get(i).gp.equals(this)) {
        return true;
      }
    }
    return false;
  }

  // adds the given gamepiece to this gamepiece's neighbors.
  void addNeighbor(GamePiece gp) {
    this.neighbors.add(gp);
  }

  // removes the given gamepiece from this gamepiece's neighbors.
  void removeNeighbor(GamePiece gp) {
    this.neighbors.remove(gp);
  }

  // lights the cells within the radius of the power station
  // NOTE: by design, we have decided to have the radius include this gamepiece.
  void lightCells(int radius) {
    this.lightCellsHelp(radius, new ArrayList<GamePiece>());
  }

  // Loops through neighbors and keeps lighting up cells within the radius,
  // decrementing each iteration
  void lightCellsHelp(int radius, ArrayList<GamePiece> sofar) {
    if (radius > -1) {
      this.powered = radius;
      sofar.add(this);
      for (int i = 0; i < this.neighbors.size(); i++) {
        if (!sofar.contains(this.neighbors.get(i))) {
          this.neighbors.get(i).lightCellsHelp(radius - 1, sofar);
        }
      }
    }

  }

  // renders a game piece depending on its top, left, right, and bottom
  WorldImage draw(int size) {
    Color color = Color.LIGHT_GRAY;
    if (this.powered != 0) {
      color = new Color(255 - 80 / this.powered, 255 - 80 / this.powered, 0);
    }

    WorldImage tempImg = new OverlayImage(
        new RectangleImage(size, size, OutlineMode.OUTLINE, Color.BLACK),
        new RectangleImage(size, size, OutlineMode.SOLID, Color.DARK_GRAY));

    if (this.right) {
      WorldImage wire = new RectangleImage(this.wireSize, 5, OutlineMode.SOLID, color);
      tempImg = new OverlayOffsetImage(wire, -size / 4, 0, tempImg);
    }
    if (this.left) {
      WorldImage wire = new RectangleImage(this.wireSize, 5, OutlineMode.SOLID, color);
      tempImg = new OverlayOffsetImage(wire, size / 4, 0, tempImg);
    }
    if (this.top) {
      WorldImage wire = new RectangleImage(5, this.wireSize, OutlineMode.SOLID, color);
      tempImg = new OverlayOffsetImage(wire, 0, size / 4, tempImg);
    }
    if (this.bottom) {
      WorldImage wire = new RectangleImage(5, this.wireSize, OutlineMode.SOLID, color);
      tempImg = new OverlayOffsetImage(wire, 0, -size / 4, tempImg);
    }
    if (this.powerStation) {
      StarImage starImg = new StarImage(20, OutlineMode.SOLID, Color.YELLOW);
      tempImg = new OverlayImage(starImg, tempImg);
    }
    return tempImg;
  }

  // rotates a game piece
  void rotate() {
    boolean temp1 = this.top;
    boolean temp2 = this.right;
    boolean temp3 = this.bottom;
    this.top = this.left;
    this.right = temp1;
    this.bottom = temp2;
    this.left = temp3;
  }

  // determines if a game piece is connected to the left
  boolean isConnectedLeft(GamePiece gp) {
    return this.left && gp.right;
  }

  // determines if a game piece is connected to the right
  boolean isConnectedRight(GamePiece gp) {
    return this.right && gp.left;
  }

  // determines if a game piece is connected to the top
  boolean isConnectedTop(GamePiece gp) {
    return this.top && gp.bottom;
  }

  // determines if a game piece is connected to the bottom
  boolean isConnectedBottom(GamePiece gp) {
    return this.bottom && gp.top;
  }
}

// class representing an edge for a tree representation
class Edge {
  GamePiece fromNode;
  GamePiece toNode;
  int weight;

  Edge(GamePiece fromNode, GamePiece toNode, int weight) {
    this.fromNode = fromNode;
    this.toNode = toNode;
    this.weight = weight;
  }

}

// examples class for testing
class ExamplesPowerLine {

  // Example data
  GamePiece gp1;
  GamePiece gp2;
  GamePiece gp3;
  GamePiece gp4;
  GamePiece gp5;
  GamePiece gp6;
  GamePiece gp7;
  GamePiece gp8;
  GamePiece gp9;
  GamePiece gp10;
  GamePiece gp11;
  LightEmAll game1;
  LightEmAll game2;
  LightEmAll game3;

  // sets up initial data for testing
  void initData() {
    // Examples of games
    this.game1 = new LightEmAll(600, 600, 8, 10, 0);
    this.game2 = new LightEmAll(500, 500, 2, 2, 3, new Random(5));
    this.game3 = new LightEmAll(500, 500, 1, 1, -1, new Random(5));
    this.gp1 = new GamePiece(1, 1, true, true, true, true, true, 35);
    this.gp2 = new GamePiece(1, 2, true, true, true, true, false, 35);
    this.gp3 = new GamePiece(2, 1, true, true, false, false, false, 35);
    this.gp4 = new GamePiece(2, 2, true, true, false, false, false, 35);
    this.gp5 = new GamePiece(1, 1, false, false, false, false, true, 35);
    this.gp6 = new GamePiece(4, 6, false, false, true, false, false, 35);
    this.gp7 = new GamePiece(2, 1, false, false, true, false, false, 35);
    this.gp8 = new GamePiece(0, 0, true, true, true, true, true, 35);
    this.gp9 = new GamePiece(0, 1, false, false, true, true, false, 35);
    this.gp10 = new GamePiece(1, 0, true, true, true, true, false, 35);
    this.gp11 = new GamePiece(1, 1, false, false, true, true, false, 35);
  }

  // runs the big bang
  void testGame(Tester t) {
    this.initData();
    this.game1.bigBang(600, 600, 1);
  }

  EdgeComp e = new EdgeComp();
  Edge e1 = new Edge(this.gp1, this.gp2, 34);
  Edge e2 = new Edge(this.gp3, this.gp4, 34);
  Edge e3 = new Edge(this.gp1, this.gp4, 36);
  Edge e4 = new Edge(this.gp2, this.gp3, 30);
  Edge e5 = new Edge(this.gp3, this.gp4, 34);

  // tests compare in EdgeComp class
  void testEdgeComp(Tester t) {
    t.checkExpect(this.e.compare(this.e1, this.e2), 0);
    t.checkExpect(this.e.compare(this.e3, this.e2), 2);
    t.checkExpect(this.e.compare(this.e4, this.e3), -6);
  }

  // test drawTiles
  void testDrawTiles(Tester t) {
    this.initData();
    WorldImage temp = new EmptyImage();
    for (int i = 0; i < this.game2.board.size(); i++) {
      WorldImage innerTemp = new EmptyImage();
      for (int j = 0; j < this.game2.board.get(i).size(); j++) {
        innerTemp = new AboveImage(innerTemp,
            this.game2.board.get(i).get(j).draw(this.game2.tileSize));
      }
      temp = new BesideImage(temp, innerTemp);
    }
    t.checkExpect(this.game2.drawTiles(), temp);
  }

  // test getTimeText
  void testGetTimeText(Tester t) {
    this.initData();
    t.checkExpect(this.game1.getTimeText(), "Time: 0 seconds");
    t.checkExpect(this.game2.getTimeText(), "Time: 0 seconds");
    this.game1.onTick();
    t.checkExpect(this.game1.getTimeText(), "Time: 1 second");
    while (this.game1.timer < 60) {
      this.game1.onTick();
    }
    t.checkExpect(this.game1.getTimeText(), "Time: 1 minute 0 seconds");
    while (this.game1.timer < 61) {
      this.game1.onTick();
    }
    t.checkExpect(this.game1.getTimeText(), "Time: 1 minute 1 second");

  }

  // test winner
  void testWinner(Tester t) {
    this.initData();
    WorldScene scene = new WorldScene(600, 600);
    TextImage winnerText = new TextImage("You Won!", Color.GREEN);
    TextImage newGameText = new TextImage("Press space to Play Again", Color.BLACK);
    TextImage endGame = new TextImage("Press escape to exit", Color.BLACK);
    TextImage name = new TextImage("Enter Your Name: " + this.game1.name, Color.BLACK);
    WorldImage newGameButton = new RectangleImage(3 * 600 / 10, 600 / 20, OutlineMode.SOLID,
        Color.GREEN);
    scene.placeImageXY(endGame, 600 / 2, 11 * 600 / 20);
    scene.placeImageXY(winnerText, 600 / 2, 2 * 600 / 5);
    scene.placeImageXY(name, 600 / 2, 600 / 2);
    scene.placeImageXY(newGameButton, 600 / 2, 3 * 600 / 5);
    scene.placeImageXY(newGameText, 600 / 2, 3 * 600 / 5);
    t.checkExpect(this.game1.winner(), scene);
  }

  // test loser
  void testLoser(Tester t) {
    this.initData();
    WorldScene scene = new WorldScene(600, 600);
    TextImage loserText = new TextImage("You Lost!", Color.RED);
    TextImage newGameText = new TextImage("Press shift to play again", Color.BLACK);
    WorldImage newGameButton = new RectangleImage(3 * 600 / 10, 600 / 20, OutlineMode.SOLID,
        Color.RED);
    TextImage endGame = new TextImage("Press escape to exit", Color.BLACK);
    scene.placeImageXY(loserText, 600 / 2, 2 * 600 / 5);
    scene.placeImageXY(endGame, 600 / 2, 9 * 600 / 20);

    scene.placeImageXY(newGameButton, 600 / 2, 3 * 600 / 5);
    scene.placeImageXY(newGameText, 600 / 2, 3 * 600 / 5);
    t.checkExpect(this.game1.loser(), scene);

  }

  // test showSolution
  void testShowSolution(Tester t) {
    this.initData();
    this.game1.onTick();
    t.checkExpect(this.game1.timer, 1);
    t.checkExpect(this.game2.lookedAtSolution, false);
    this.game2.showSolution();
    t.checkExpect(this.game2.lookedAtSolution, true);
    t.checkExpect(this.game1.lookedAtSolution, false);
    this.game1.showSolution();
    t.checkExpect(this.game1.lookedAtSolution, true);
    t.checkExpect(this.game1.timer, 0);
    t.checkExpect(this.game2.timer, 0);
    t.checkExpect(this.game1.moves, 0);
    t.checkExpect(this.game2.moves, 0);

  }

  // test reset
  void testReset(Tester t) {
    this.initData();
    // doing some stuff to the game
    this.game1.showSolution();
    this.game1.onTick();
    t.checkExpect(this.game1.lookedAtSolution, true);
    t.checkExpect(this.game1.timer, 1);
    // resetting
    this.game1.reset();
    t.checkExpect(this.game1.timer, 0);
    t.checkExpect(this.game1.moves, 0);
    t.checkExpect(this.game1.lookedAtSolution, false);
  }

  // test newGame
  void testNewGame(Tester t) {
    this.initData();
    this.game1.showSolution();
    this.game1.onTick();
    this.game1.onKeyEvent("right");
    this.game1.onKeyEvent("down");
    t.checkExpect(this.game1.lookedAtSolution, true);
    t.checkExpect(this.game1.timer, 1);
    this.game1.newGame();
    t.checkExpect(this.game1.powerCol, 4);
    t.checkExpect(this.game1.powerRow, 0);
    t.checkExpect(this.game1.lookedAtSolution, false);
    t.checkExpect(this.game1.timer, 0);

  }

  // test isWinner
  void testIsWinner(Tester t) {
    this.initData();
    t.checkExpect(this.game1.isWinner(), false);
    t.checkExpect(this.game2.isWinner(), false);
    this.game2.showSolution();
    this.game2.onKeyEvent("down");
    t.checkExpect(this.game3.isWinner(), true);
  }

  // test writeName
  void testWriteName(Tester t) {
    this.initData();
    this.game1.writeName("K");
    t.checkExpect(this.game1.name, "");
    this.game1.writeName("k");
    t.checkExpect(this.game1.name, "k");
    this.game1.writeName("1");
    t.checkExpect(this.game1.name, "k");
    this.game1.writeName("!");
    t.checkExpect(this.game1.name, "k");

  }

  // test worldEnds
  void testWorldEnds(Tester t) {
    this.initData();
    t.checkExpect(this.game1.worldEnds(), new WorldEnd(false, this.game1.makeScene()));
    this.game1.gameOver = true;
  }

  // test makeAFinalScene
  void testMakeAFinalScene(Tester t) {
    this.initData();
    WorldScene scene = new WorldScene(600, 600);
    scene.placeImageXY(new TextImage("Game Over", Color.BLACK), 300, 300);
    t.checkExpect(this.game1.makeAFinalScene(), scene);
    WorldScene scene2 = new WorldScene(500, 500);
    scene2.placeImageXY(new TextImage("Game Over", Color.BLACK), 250, 250);
    t.checkExpect(this.game2.makeAFinalScene(), scene2);
  }

  // test union
  void testUnion(Tester t) {
    this.initData();
    HashMap<GamePiece, GamePiece> hm = new HashMap<GamePiece, GamePiece>();
    hm.put(this.gp2, this.gp1);
    hm.put(this.gp3, this.gp2);
    this.game1.union(hm, this.gp1, this.gp2);
    t.checkExpect(hm.size(), 2);
  }

  // test for draw
  void testDraw(Tester t) {
    this.initData();
    t.checkExpect(this.gp5.draw(70),
        new OverlayImage(new StarImage(20, OutlineMode.SOLID, Color.YELLOW),
            new OverlayImage(new RectangleImage(70, 70, OutlineMode.OUTLINE, Color.BLACK),
                new RectangleImage(70, 70, OutlineMode.SOLID, Color.DARK_GRAY))));
    t.checkExpect(this.gp4.draw(70),
        new OverlayOffsetImage(new RectangleImage(35, 5, OutlineMode.SOLID, Color.LIGHT_GRAY),
            70 / 4, 0,
            new OverlayOffsetImage(new RectangleImage(35, 5, OutlineMode.SOLID, Color.LIGHT_GRAY),
                -70 / 4, 0,
                new OverlayImage(new RectangleImage(70, 70, OutlineMode.OUTLINE, Color.BLACK),
                    new RectangleImage(70, 70, OutlineMode.SOLID, Color.DARK_GRAY)))));
    t.checkExpect(this.gp6.draw(70),
        new OverlayOffsetImage(new RectangleImage(5, 35, OutlineMode.SOLID, Color.LIGHT_GRAY), 0,
            70 / 4, new OverlayImage(new RectangleImage(70, 70, OutlineMode.OUTLINE, Color.BLACK),
                new RectangleImage(70, 70, OutlineMode.SOLID, Color.DARK_GRAY))));
  }

  // test for rotate
  void testRotate(Tester t) {
    this.initData();
    this.gp1.rotate();
    // shows that the powerStation has not been changed
    t.checkExpect(this.gp1.powerStation, true);
    t.checkExpect(this.gp1.top, true);
    t.checkExpect(this.gp1.bottom, true);
    t.checkExpect(this.gp1.right, true);
    t.checkExpect(this.gp1.left, true);
    this.gp2.rotate();
    t.checkExpect(this.gp2.left, true);
    t.checkExpect(this.gp2.top, true);
    t.checkExpect(this.gp2.right, true);
    t.checkExpect(this.gp2.bottom, true);
    t.checkExpect(this.gp2.powerStation, false);
    this.gp3.rotate();
    t.checkExpect(this.gp3.left, false);
    t.checkExpect(this.gp3.top, true);
    t.checkExpect(this.gp3.right, false);
    t.checkExpect(this.gp3.bottom, true);
  }

  // test for isConnectedLeft
  void testIsConnectedLeft(Tester t) {
    this.initData();
    t.checkExpect(this.gp1.isConnectedLeft(this.gp6), false);
    t.checkExpect(this.gp1.isConnectedLeft(this.gp2), true);
    t.checkExpect(this.gp2.isConnectedLeft(this.gp1), true);
    t.checkExpect(this.gp3.isConnectedLeft(this.gp6), false);
    t.checkExpect(this.gp3.isConnectedLeft(this.gp2), true);
    t.checkExpect(this.gp3.isConnectedLeft(this.gp4), true);
    t.checkExpect(this.gp4.isConnectedLeft(this.gp3), true);

  }

  // test for isConnectedBottom
  void testIsConnectedBottom(Tester t) {
    this.initData();
    t.checkExpect(this.gp1.isConnectedBottom(this.gp6), true);
    t.checkExpect(this.gp1.isConnectedBottom(this.gp2), true);
    t.checkExpect(this.gp3.isConnectedBottom(this.gp6), false);
    t.checkExpect(this.gp3.isConnectedBottom(this.gp2), false);
    t.checkExpect(this.gp3.isConnectedBottom(this.gp4), false);
    t.checkExpect(this.gp3.isConnectedBottom(this.gp4), false);
    t.checkExpect(this.gp3.isConnectedBottom(this.gp1), false);
    t.checkExpect(this.gp1.isConnectedBottom(this.gp7), true);

  }

  // test for isConnectedTop
  void testIsConnectedTop(Tester t) {
    this.initData();
    t.checkExpect(this.gp1.isConnectedTop(this.gp6), false);
    t.checkExpect(this.gp1.isConnectedTop(this.gp2), true);
    t.checkExpect(this.gp3.isConnectedTop(this.gp6), false);
    t.checkExpect(this.gp3.isConnectedTop(this.gp2), false);
    t.checkExpect(this.gp3.isConnectedTop(this.gp4), false);
    t.checkExpect(this.gp3.isConnectedBottom(this.gp1), false);
    t.checkExpect(this.gp1.isConnectedBottom(this.gp3), false);

  }

  // test for isConnectedRight
  void testIsConnectedRight(Tester t) {
    this.initData();
    t.checkExpect(this.gp1.isConnectedRight(this.gp6), false);
    t.checkExpect(this.gp1.isConnectedRight(this.gp2), true);
    t.checkExpect(this.gp2.isConnectedRight(this.gp1), true);
    t.checkExpect(this.gp3.isConnectedRight(this.gp6), false);
    t.checkExpect(this.gp3.isConnectedRight(this.gp2), true);
    t.checkExpect(this.gp3.isConnectedRight(this.gp4), true);
    t.checkExpect(this.gp4.isConnectedRight(this.gp3), true);

  }

  // test for lightCells
  void testLightCells(Tester t) {
    this.initData();
    this.gp1.lightCells(1);
    t.checkExpect(this.gp1.powered, 1);
    this.gp2.lightCells(10);
    t.checkExpect(this.gp2.powered, 10);
    this.gp3.lightCells(8);
    t.checkExpect(this.gp3.powered, 8);

  }

  // test for lightCellsHelp
  void testLightCellsHelp(Tester t) {
    this.initData();
    this.gp1.lightCellsHelp(1, new ArrayList<GamePiece>());
    t.checkExpect(this.gp1.powered, 1);
    this.gp2.lightCellsHelp(10, new ArrayList<GamePiece>());
    t.checkExpect(this.gp2.powered, 10);
  }

  // test for removeNeighbors GamePiece class
  void testRemoveNeighborGamePiece(Tester t) {
    this.initData();
    // adding neighbors first
    t.checkExpect(this.gp1.neighbors.size(), 0);
    this.gp1.addNeighbor(this.gp2);
    this.gp1.addNeighbor(this.gp3);
    this.gp1.addNeighbor(this.gp10);
    t.checkExpect(this.gp1.neighbors.size(), 3);
    // now testing removeNeighbor
    this.gp1.removeNeighbor(this.gp3);
    t.checkExpect(this.gp1.neighbors.size(), 2);
    this.gp1.removeNeighbor(this.gp2);
    t.checkExpect(this.gp1.neighbors.size(), 1);
    this.gp1.removeNeighbor(this.gp10);
    t.checkExpect(this.gp1.neighbors.size(), 0);

  }

  // testing onTick
  void testOnTick(Tester t) {
    this.initData();
    int temp1 = this.game1.timer;
    this.game1.onTick();
    t.checkExpect(this.game1.timer, temp1 + 1);
    this.game1.onTick();
    t.checkExpect(this.game1.timer, temp1 + 2);
    int temp2 = this.game2.timer;
    this.game2.onTick();
    t.checkExpect(this.game2.timer, temp2 + 1);
    int temp3 = this.game3.timer;
    this.game3.onTick();
    t.checkExpect(this.game3.timer, temp3 + 1);
  }

  // test for removeNeighbors LightEmAll class
  void testRemoveNeighbors(Tester t) {
    this.initData();
    this.game1.removeNeighbors();
    t.checkExpect(this.game1.board.get(0).get(0).neighbors, new ArrayList<GamePiece>());
    t.checkExpect(this.game1.board.get(0).get(1).neighbors, new ArrayList<GamePiece>());
    t.checkExpect(this.game1.board.get(1).get(1).neighbors, new ArrayList<GamePiece>());
    t.checkExpect(this.game1.board.get(6).get(5).neighbors, new ArrayList<GamePiece>());
    ArrayList<GamePiece> neighbors1 = this.game1.board.get(0).get(0).neighbors;
    // adding neighbors
    neighbors1.add(this.gp1);
    neighbors1.add(this.gp2);
    neighbors1.add(this.gp4);
    neighbors1.add(this.gp10);
    // shows that neighbors are there
    t.checkExpect(this.game1.board.get(0).get(0).neighbors.get(0), this.gp1);
    t.checkExpect(this.game1.board.get(0).get(0).neighbors.get(1), this.gp2);
    t.checkExpect(this.game1.board.get(0).get(0).neighbors.get(2), this.gp4);
    t.checkExpect(this.game1.board.get(0).get(0).neighbors.get(3), this.gp10);
    // removing neighbors
    this.game1.removeNeighbors();
    t.checkExpect(this.game1.board.get(0).get(0).neighbors, new ArrayList<GamePiece>());

  }

  void testKruskalAlgos(Tester t) {
    LightEmAll testKruskal = new LightEmAll(600, 600, 10, 10, 0, new Random(5));
    HashMap<GamePiece, GamePiece> representatives = new HashMap<GamePiece, GamePiece>();

    for (int i = 0; i < testKruskal.board.size(); i++) {
      for (int j = 0; j < testKruskal.board.get(i).size(); j++) {
        GamePiece curr = testKruskal.board.get(i).get(j);
        representatives.put(curr, curr);
      }
    }

    ArrayList<Edge> edgesInTree = new ArrayList<Edge>();
    EdgeComp comp = new EdgeComp();
    ArrayList<Edge> worklist = testKruskal.generateEdges();
    worklist.sort(comp);

    while (worklist.size() > 0) {
      Edge current = worklist.get(0);
      if (representatives.get(current.fromNode).equals(representatives.get(current.toNode))) {
        worklist.remove(current);
      } else {
        edgesInTree.add(worklist.remove(0));
        testKruskal.union(representatives, representatives.get(current.fromNode),
            representatives.get(current.toNode));
      }
    }
    testKruskal = new LightEmAll(600, 600, 10, 10, 0, new Random(5));

    t.checkExpect(testKruskal.kruskalAlgos().size(), 99);

  }

  // testing generateEdges
  void testGenerateEdges(Tester t) {
    this.initData();
    t.checkExpect(this.game1.generateEdges().size(), 142);
    t.checkExpect(this.game2.generateEdges().size(), 4);
    t.checkExpect(this.game3.generateEdges().size(), 0);
  }

  void testFindGroupOfGamePiece(Tester t) {
    HashMap<GamePiece, GamePiece> testHash = new HashMap<GamePiece, GamePiece>();
    testHash.put(this.gp1, this.gp2);
    GamePiece x = new GamePiece(0, 0, true, true, true, true, true, 30);
    LightEmAll testFindGroupOfGamePiece = new LightEmAll(600, 600, 10, 10, 0, new Random(5));
    ArrayList<GamePiece> gpInGroup = new ArrayList<GamePiece>();
    for (int i = 0; i < testFindGroupOfGamePiece.board.size(); i++) {
      for (int j = 0; j < testFindGroupOfGamePiece.board.get(i).size(); j++) {
        GamePiece curr = testFindGroupOfGamePiece.board.get(i).get(j);
        if (testHash.get(curr) != null && testHash.get(curr).equals(x)) {
          gpInGroup.add(curr);
        }
      }
    }
    testFindGroupOfGamePiece = new LightEmAll(600, 600, 10, 10, 0, new Random(5));
    HashMap<GamePiece, GamePiece> reps = new HashMap<GamePiece, GamePiece>();
    reps.put(this.gp1, this.gp2);
    t.checkExpect(testFindGroupOfGamePiece
        .findGroupOfGamePiece(reps, new GamePiece(0, 0, true, true, true, true, true, 30)).size(),
        0);
  }

  void testChangeValues(Tester t) {
    LightEmAll testChangeValues = new LightEmAll(600, 600, 10, 10, 0, new Random(5));
    HashMap<GamePiece, GamePiece> testHash = new HashMap<GamePiece, GamePiece>();
    testHash.put(this.gp1, this.gp2);
    GamePiece x = new GamePiece(0, 0, true, true, true, true, true, 30);
    GamePiece y = new GamePiece(0, 0, true, true, true, true, true, 30);
    ArrayList<GamePiece> xGroup = testChangeValues.findGroupOfGamePiece(testHash, x);
    for (int i = 0; i < xGroup.size(); i++) {
      testHash.remove(xGroup.get(i));
      testHash.put(xGroup.get(i), y);
    }
    testChangeValues = new LightEmAll(600, 600, 10, 10, 0, new Random(5));
    HashMap<GamePiece, GamePiece> reps = new HashMap<GamePiece, GamePiece>();
    reps.put(this.gp1, this.gp2);
    t.checkExpect(
        testChangeValues.changeValues(reps, new GamePiece(0, 0, true, true, true, true, true, 30),
            new GamePiece(0, 0, true, true, true, true, true, 30)).size(),
        1);
  }

  void testBfs(Tester t) {
    LightEmAll testBfs = new LightEmAll(600, 600, 10, 10, 0, new Random(5));
    GamePiece curr = testBfs.board.get(5).get(0);
    ArrayList<GamePieceDepth> sofar = new ArrayList<GamePieceDepth>();
    Queue<GamePieceDepth> queue = new LinkedList<GamePieceDepth>();
    queue.add(new GamePieceDepth(curr, 0));
    GamePieceDepth removed = null;
    while (!queue.isEmpty()) {
      removed = queue.remove();
      for (GamePiece gamePiece : removed.gp.neighbors) {
        if (!gamePiece.gamePieceInDepth(sofar)) {
          sofar.add(removed);
          queue.add(new GamePieceDepth(gamePiece, removed.depth + 1));
        }
      }
    }
    testBfs = new LightEmAll(600, 600, 10, 10, 0, new Random(5));

    // t.checkExpect(testBfs.bfs(new Posn(5,0)).depth, removed.depth);

  }

  void getRadius(Tester t) {
    LightEmAll testGetRadius = new LightEmAll(600, 600, 10, 10, 0, new Random(5));
    GamePieceDepth furthestFirst = testGetRadius.bfs(new Posn(0, 5));
    GamePieceDepth furthestSecond = testGetRadius.bfs(furthestFirst.getCoordinates());

    testGetRadius = new LightEmAll(600, 600, 10, 10, 0, new Random(5));
    t.checkExpect(testGetRadius.getRadius(), furthestSecond.depth / 2 + 1);
  }

  // test AddNeighbors
  void testAddNeighbors(Tester t) {
    LightEmAll testAddNeighbors = new LightEmAll(600, 600, 10, 10, 0, new Random(5));
    testAddNeighbors.removeNeighbors();
    for (int i = 0; i < testAddNeighbors.board.size(); i++) {
      for (int j = 0; j < testAddNeighbors.board.get(i).size(); j++) {
        GamePiece curr = testAddNeighbors.board.get(i).get(j);
        if (i > 0) {
          if (curr.isConnectedLeft(testAddNeighbors.board.get(i - 1).get(j))) {
            curr.addNeighbor(testAddNeighbors.board.get(i - 1).get(j));
          }
        }
        if (j > 0) {
          if (curr.isConnectedTop(testAddNeighbors.board.get(i).get(j - 1))) {
            curr.addNeighbor(testAddNeighbors.board.get(i).get(j - 1));
          }
        }
        if (i < testAddNeighbors.board.size() - 1) {
          if (curr.isConnectedRight(testAddNeighbors.board.get(i + 1).get(j))) {
            curr.addNeighbor(testAddNeighbors.board.get(i + 1).get(j));
          }
        }
        if (j < testAddNeighbors.board.get(i).size() - 1) {
          if (curr.isConnectedBottom(testAddNeighbors.board.get(i).get(j + 1))) {
            curr.addNeighbor(testAddNeighbors.board.get(i).get(j + 1));
          }
        }
      }
    }

    testAddNeighbors = new LightEmAll(600, 600, 10, 10, 0, new Random(5));
    t.checkExpect(testAddNeighbors.board.get(0).get(0).neighbors.size(), 0);
    t.checkExpect(testAddNeighbors.board.get(1).get(0).neighbors.size(), 1);
    t.checkExpect(testAddNeighbors.board.get(0).get(1).neighbors.size(), 0);
  }

  // test gamePieceInDepth
  void testGamePieceInDepth(Tester t) {
    this.initData();
    ArrayList<GamePieceDepth> arr1 = new ArrayList<GamePieceDepth>();
    t.checkExpect(this.gp1.gamePieceInDepth(arr1), false);
    t.checkExpect(this.gp2.gamePieceInDepth(arr1), false);
    t.checkExpect(this.gp3.gamePieceInDepth(arr1), false);
    t.checkExpect(this.gp4.gamePieceInDepth(arr1), false);
    t.checkExpect(this.gp5.gamePieceInDepth(arr1), false);
    arr1.add(new GamePieceDepth(this.gp1, 1));
    t.checkExpect(this.gp1.gamePieceInDepth(arr1), true);
    t.checkExpect(this.gp2.gamePieceInDepth(arr1), false);
    t.checkExpect(this.gp3.gamePieceInDepth(arr1), false);
    t.checkExpect(this.gp4.gamePieceInDepth(arr1), false);
    t.checkExpect(this.gp5.gamePieceInDepth(arr1), false);
    arr1.add(new GamePieceDepth(this.gp2, 6));
    t.checkExpect(this.gp1.gamePieceInDepth(arr1), true);
    t.checkExpect(this.gp2.gamePieceInDepth(arr1), true);
    t.checkExpect(this.gp3.gamePieceInDepth(arr1), false);
    t.checkExpect(this.gp4.gamePieceInDepth(arr1), false);
    t.checkExpect(this.gp5.gamePieceInDepth(arr1), false);

  }

  // test getCoordinates
  void testGetCoordinates(Tester t) {
    this.initData();
    t.checkExpect(new GamePieceDepth(this.gp1, 0).getCoordinates(), new Posn(1, 1));
    t.checkExpect(new GamePieceDepth(this.gp2, 1).getCoordinates(), new Posn(1, 2));
    t.checkExpect(new GamePieceDepth(this.gp3, 2).getCoordinates(), new Posn(2, 1));
    t.checkExpect(new GamePieceDepth(this.gp4, 7).getCoordinates(), new Posn(2, 2));
    t.checkExpect(new GamePieceDepth(this.gp5, 10).getCoordinates(), new Posn(1, 1));
    t.checkExpect(new GamePieceDepth(this.gp6, 20).getCoordinates(), new Posn(4, 6));
    t.checkExpect(new GamePieceDepth(this.gp7, 6).getCoordinates(), new Posn(2, 1));
  }

  // test turnGamePieceOff
  void testGamePieceOff(Tester t) {
    this.initData();
    this.game2.turnGamePieceOff();
    t.checkExpect(this.game2.board.get(0).get(0).powered, 0);
    t.checkExpect(this.game2.board.get(1).get(1).powered, 0);
    t.checkExpect(this.game2.board.get(0).get(1).powered, 0);
  }

  // test createBoardWithMst
  void testCreateBoardMst(Tester t) {
    LightEmAll testCreateBoardMst = new LightEmAll(600, 600, 10, 10, 0, new Random(5));
    for (int i = 0; i < testCreateBoardMst.mst.size(); i++) {
      GamePiece curr1 = testCreateBoardMst.mst.get(i).fromNode;
      GamePiece curr2 = testCreateBoardMst.mst.get(i).toNode;

      if (curr1.row == curr2.row) {
        if (curr1.col == curr2.col + 1) {
          testCreateBoardMst.board.get(curr1.row).get(curr1.col).top = true;
          testCreateBoardMst.board.get(curr2.row).get(curr2.col).bottom = true;
        } else {
          testCreateBoardMst.board.get(curr1.row).get(curr1.col).bottom = true;
          testCreateBoardMst.board.get(curr2.row).get(curr2.col).top = true;
        }
      }
      if (curr1.col == curr2.col) {
        if (curr1.row == curr2.row + 1) {
          testCreateBoardMst.board.get(curr1.row).get(curr1.col).left = true;
          testCreateBoardMst.board.get(curr2.row).get(curr2.col).right = true;
        } else {
          testCreateBoardMst.board.get(curr1.row).get(curr1.col).right = true;
          testCreateBoardMst.board.get(curr1.row).get(curr2.col).left = true;
        }
      }
    }
    t.checkExpect(testCreateBoardMst.mst.size(), 99);
  }

  // test createBoard
  void testCreateBoard(Tester t) {
    LightEmAll testCreateBoard = new LightEmAll(600, 600, 10, 10, 0, new Random(5));

    t.checkExpect(testCreateBoard.createBoard().size(), 10);
    t.checkExpect(testCreateBoard.createBoard().get(0).size(), 10);
  }

  // test saveCurrState
  void testSaveCurrState(Tester t) {
    LightEmAll testSaveCurrState = new LightEmAll(600, 600, 10, 10, 0, new Random(5));
    testSaveCurrState.saveCurrState();
    t.checkExpect(testSaveCurrState.currState.get(0).size(), 10);
    t.checkExpect(testSaveCurrState.currState.size(), 20);
  }

  void testRotations(Tester t) {
    LightEmAll testRotations = new LightEmAll(600, 600, 10, 10, 0, new Random(5));
    int moves = 0;
    for (int i = 0; i < testRotations.board.size(); i++) {
      for (int j = 0; j < testRotations.board.get(i).size(); j++) {
        int rotations = testRotations.random.nextInt(4);
        moves = moves + 4 - rotations;
        while (rotations > 0) {
          testRotations.board.get(i).get(j).rotate();
          rotations--;
        }

      }

    }
    testRotations.removeNeighbors();
    testRotations.addNeighbors();
    testRotations.turnGamePieceOff();
    testRotations.board.get(testRotations.powerCol).get(testRotations.powerRow)
        .lightCells(testRotations.radius + 1);
    int ans = moves + testRotations.radius;

    testRotations = new LightEmAll(600, 600, 10, 10, 0, new Random(5));
    t.checkExpect(testRotations.rotations(), ans);
  }

  // test for makeScene
  void testMakeScene(Tester t) {
    LightEmAll testMakeScene = new LightEmAll(600, 600, 10, 10, 0, new Random(5));
    WorldScene scene = new WorldScene(testMakeScene.width, testMakeScene.height);

    scene.placeImageXY(testMakeScene.drawTiles(), testMakeScene.width / 2,
        testMakeScene.height / 2);
    TextImage timeCount = new TextImage(testMakeScene.getTimeText(), Color.BLACK);
    TextImage movesCount = new TextImage("Number of Moves: " + testMakeScene.moves, Color.BLACK);
    TextImage movesNeeded = new TextImage("Number of Moves Needed: " + testMakeScene.numMovesNeeded,
        Color.BLACK);
    TextImage resetText = new TextImage("Press shift to Reset", Color.BLACK);
    WorldImage resetButton = new RectangleImage(testMakeScene.width / 4, testMakeScene.height / 20,
        OutlineMode.OUTLINE, Color.BLUE);
    int userMovesRemaining = 3 * testMakeScene.numMovesNeeded / 2 + testMakeScene.radius
        - testMakeScene.moves;
    TextImage userMovesNeeded = new TextImage("Number of Moves Left: " + userMovesRemaining,
        Color.BLACK);
    TextImage showSolution = new TextImage("Show Solution", Color.BLACK);
    WorldImage solutionButton = new RectangleImage(testMakeScene.width / 4,
        testMakeScene.height / 20, OutlineMode.OUTLINE, Color.RED);
    scene.placeImageXY(resetText, (int) (testMakeScene.width / 2),
        (int) (.025 * testMakeScene.height));
    scene.placeImageXY(resetButton, (int) (testMakeScene.width / 2),
        (int) (.025 * testMakeScene.height));
    scene.placeImageXY(timeCount, (int) (testMakeScene.width / 7),
        (int) (.98 * testMakeScene.height));
    scene.placeImageXY(movesCount, (int) (testMakeScene.width / 2),
        (int) (.98 * testMakeScene.height));
    scene.placeImageXY(movesNeeded, (int) (5 * testMakeScene.width / 6),
        (int) (.98 * testMakeScene.height));
    scene.placeImageXY(userMovesNeeded, testMakeScene.width / 6,
        (int) (.025 * testMakeScene.height));
    scene.placeImageXY(showSolution, (int) (4 * testMakeScene.width / 5),
        (int) (.025 * testMakeScene.height));
    scene.placeImageXY(solutionButton, (int) (4 * testMakeScene.width / 5),
        (int) (.025 * testMakeScene.height));
    if (3 * testMakeScene.numMovesNeeded / 2 + testMakeScene.radius - testMakeScene.moves < 0) {
      scene = testMakeScene.loser();
    }
    if (testMakeScene.isWinner()) {
      scene = testMakeScene.winner();
    }
    t.checkExpect(testMakeScene.makeScene(), scene);
  }

  // testOnMouseClicked
  void testOnMouseClicked(Tester t) {
    this.initData();
    t.checkExpect(this.game2.board.get(0).get(0).powerStation, false);
    t.checkExpect(this.game2.board.get(0).get(0).top, false);
    t.checkExpect(this.game2.board.get(0).get(0).bottom, true);
    t.checkExpect(this.game2.board.get(0).get(0).left, true);
    t.checkExpect(this.game2.board.get(0).get(0).right, false);
    this.game2.onMouseClicked(new Posn(1, 1), "RightButton");
    t.checkExpect(this.game2.board.get(0).get(0).bottom, true);
    this.game2.onMouseClicked(new Posn(1, 1), "LeftButton");
    t.checkExpect(this.game2.board.get(0).get(0).top, false);
    t.checkExpect(this.game2.board.get(0).get(0).bottom, true);
    t.checkExpect(this.game2.board.get(0).get(0).left, true);
    t.checkExpect(this.game2.board.get(0).get(0).right, false);

    t.checkExpect(this.game2.board.get(1).get(1).powerStation, false);
    t.checkExpect(this.game2.board.get(1).get(1).top, false);
    t.checkExpect(this.game2.board.get(1).get(1).bottom, false);
    t.checkExpect(this.game2.board.get(1).get(1).left, true);
    t.checkExpect(this.game2.board.get(1).get(1).right, false);
    this.game2.onMouseClicked(new Posn(2, 2), "LeftButton");
    t.checkExpect(this.game2.board.get(1).get(1).right, false);

  }

  // test for onKeyEvent
  void testOnKeyEvent(Tester t) {
    this.initData();
    this.game1.onKeyEvent("a");
    t.checkExpect(this.game1.board.get(5).get(0).powerStation, false);
    this.game1.onKeyEvent("up");
    t.checkExpect(this.game1.board.get(5).get(0).powerStation, false);
    this.game1.onKeyEvent("down");
    t.checkExpect(this.game1.board.get(5).get(0).powerStation, false);
    t.checkExpect(this.game1.board.get(5).get(1).powerStation, false);
    this.initData();
    this.game1.onKeyEvent("left");
    t.checkExpect(this.game1.board.get(0).get(0).powerStation, false);
  }

  // test for addNeighbors GamePiece class
  void testAddNeighborGamePiece(Tester t) {
    this.initData();
    t.checkExpect(this.gp1.neighbors.size(), 0);
    this.gp1.addNeighbor(this.gp2);
    this.gp1.addNeighbor(this.gp3);
    this.gp1.addNeighbor(this.gp10);
    t.checkExpect(this.gp1.neighbors.size(), 3);
  }

}


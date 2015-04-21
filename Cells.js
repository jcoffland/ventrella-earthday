
var canvasID = document.getElementById( 'CellsCanvas' );
var canvas = canvasID.getContext( '2d' );

function Cells()
{	
	//---------------------------------------
	// constants
	//---------------------------------------
	var MILLISECONDS_PER_UPDATE = 10;
	var WINDOW_WIDTH			= 800;
	var WINDOW_HEIGHT			= 600;
	var ROOT3_2     	        = Math.sqrt(3) / 2;
	var ONE_HALF                = 0.5;
	var RES				    	= 150;
	var AVERAGE_RANDOM_FITNESS	= 0.4;
	var MAX_NEIGHBORS			= 6;
	var NUM_RULES				= 40;
	var NUM_RULE_ELEMENTS		= 4;
	var NUM_INDIVIDUALS			= 50;
	var NUM_STATES				= 7;
	var MAX_AGE					= 3;
	var MAX_NEIGHBOR_COUNT		= 3;
	var FITNESS_DECAY			= 0.96;
	var RATING_SCALE			= 1.0;
	var CROSSOVER_RATE			= 0.1;
	var MUTATION_RATE			= 0.03;	
    var NUM_ICOSA_POINTS    	= 12;
    var NUM_GEODESICS		    = 6;
    var MAX_CELLS			    = 50000;
	var SCALE                   = 245;
	var CELL_SIZE               = 10;
    var	MIN_NEIGHBOR_DISTANCE	= 0.15;
    var MOUSE_FUDGE_SHIFT       = 10;

/*
	var BLACK 					= "rgb(   0,   0,   0 )"
	var RED 					= "rgb( 200,  60,  60 )"
	var ORANGE					= "rgb( 200, 160,  50 )"
	var YELLOW					= "rgb( 230, 230,  50 )"
	var LIGHT_GREEN			    = "rgb( 150, 260, 150 )"
	var DARK_GREEN				= "rgb(  30, 120,  30 )"
	var LIGHT_BLUE				= "rgb( 100, 170, 255 )"
	var DARK_BLUE				= "rgb(  20,  30,  60 )"
	var WHITE   				= "rgb( 200, 200, 200 )"
	var GRAY    				= "rgb( 150, 150, 150 )"
	var BLUE					= "rgb(  90,  90, 255 )"
	var VIOLET  				= "rgb( 170,  90, 200 )"
	var LIGHT_GRAY				= "rgb( 150, 150, 150 )"
	var DARK_GRAY				= "rgb(  50,  50,  50 )"
	var LIGHT_BROWN   			= "rgb( 160, 130, 100 )"
	var DARK_BROWN   			= "rgb( 100,  60,  30 )"
	*/
	
	var BLACK 					= "rgb(   0,   0,   0 )"
	var LIGHT_GREEN			    = "rgb( 150, 260, 150 )"
	var DARK_GREEN				= "rgb(  30, 120,  30 )"
	var LIGHT_BLUE				= "rgb( 100, 170, 255 )"
	var DARK_BLUE				= "rgb(  20,  30,  60 )"
	var WHITE   				= "rgb( 200, 200, 200 )"
	var GRAY    				= "rgb( 150, 150, 150 )"
	var BLUE					= "rgb(  90,  90, 255 )"
	var LIGHT_GRAY				= "rgb( 150, 150, 150 )"
	var DARK_GRAY				= "rgb(  50,  50,  50 )"
	var LIGHT_BROWN   			= "rgb( 160, 130, 100 )"
	var DARK_BROWN   			= "rgb( 100,  60,  30 )"
	
	
	var BUTTON_LEFT				= WINDOW_WIDTH + 23;
	var BUTTON_TOP				= 90;
	var BUTTON_WIDTH 			= 85;
	var BUTTON_HEIGHT			= 30;
	var BUTTON_MARGIN			= 5;
	var NUM_BUTTONS				= 11;
	
	function Button()
	{
		this.x = 0;
		this.y = 0
		this.w = 0;
		this.h = 0;
	}	
	
	var button 		= new Array( Button );
	var mouseX 		= 0;
	var	mouseY 		= 0;
	var parent1		= 0;
	var parent2		= 0;
	var mouseIsDown = false;
	var color 		= [NUM_STATES];	
	var num 		= [NUM_STATES];	
    var rotation    = 0;
    var rotationSin = 0;
    var rotationCos = 0;
    
    var neighborsFound = false;
	
	color[0] = DARK_BLUE;
	color[1] = LIGHT_BLUE;
	color[2] = DARK_GREEN;
	color[3] = LIGHT_BLUE;
	color[4] = WHITE;
	color[5] = LIGHT_BROWN;
	color[6] = DARK_BROWN;
	color[7] = LIGHT_BROWN;
	color[8] = DARK_GRAY;	

    this.clock = 0;	

	var cellSize = WINDOW_WIDTH / RES;

	var currentIndividual = 0;
	
	var numGenesPerIndividual = NUM_STATES + NUM_RULES * NUM_RULE_ELEMENTS;
	
	//------------------------------------
	// create the cell array
	//------------------------------------
	function Cell()
	{
		this.x  	      = 0.0; 
		this.y  	      = 0.0; 
		this.z  	      = 0.0; 
		this.xv 	      = 0.0; 
		this.yv 	      = 0.0; 
		this.zv 	      = 0.0; 
		this.age          = 0;
		this.state        = 0;
		this.backup       = 0;
		this.initialized  = false;
		this.numNeighbors = 0;
		this.neighbor = new Array(MAX_NEIGHBORS);
		this.birth    = new Array(MAX_NEIGHBORS);		
	}	
	
	this.Xcenter = document.body.clientWidth / 2;
	
	this.numCells = MAX_CELLS;
	
    this.earthImage = new Image();
    this.earthImage.src = 'earth.png';
	
	this.cell = new Array( MAX_CELLS );
	
	for (var c=0; c<MAX_CELLS; c++)
	{
		this.cell[c] = new Cell();
		
    	for (var n=0; n<MAX_NEIGHBORS; n++)
	    {
		    this.cell[c].neighbor[n] = -1;
            this.cell[c].birth[n] = false;
    	}				
	}	
  	
	//------------------------------------
	// create the rule arrays
	//------------------------------------
	var ruleState  = new Array(NUM_RULES);
	var ruleCell   = new Array(NUM_RULES);
	var ruleNum    = new Array(NUM_RULES);
	var ruleResult = new Array(NUM_RULES);
	var ruleAge    = new Array(NUM_STATES);
	
	//------------------------------------
	// create the num array
	//------------------------------------
	var num = new Array(NUM_STATES);
	
	//-------------------------------------------------
	// create the gene and fitness arrays
	//-------------------------------------------------
	var gene    = new Array( NUM_INDIVIDUALS );
	var fitness = new Array( NUM_INDIVIDUALS );
	
	for (var i = 0; i < NUM_INDIVIDUALS; i++) 
	{
		gene[i] = new Array(numGenesPerIndividual);
	}

	//---------------------------------------------
	// randomize the gene and fitness arrays
	//---------------------------------------------
	for (var i = 0; i < NUM_INDIVIDUALS; i++) 
	{	
		var g = 0;
		for (var s = 0; s < NUM_STATES; s++) 
		{
			gene[i][g] = Math.floor( Math.random() * MAX_AGE ); g++; // ruleAge
		}
		
		for (var r = 0; r < NUM_RULES; r++) 
		{
			gene[i][g] =     Math.floor( Math.random() * (NUM_STATES  )		); g++; // ruleCell
			gene[i][g] = 1 + Math.floor( Math.random() * (NUM_STATES-1)    	); g++; // ruleState
			gene[i][g] = 1 + Math.floor( Math.random() * MAX_NEIGHBOR_COUNT	); g++; // ruleNum
			gene[i][g] =     Math.floor( Math.random() * (NUM_STATES  )		); g++; // ruleResult
		}			

		if ( g != numGenesPerIndividual ) 
		{
			console.log( "hey, problem: numGenes is " + numGenesPerIndividual + " but I counted " + g );
		}
	}
	
	
	//______________________________________________________________________________
    this.arrangeButtons = function()	
	{
        var xx = BUTTON_LEFT;
        var yy = BUTTON_TOP;
        var h  = BUTTON_HEIGHT * 1.2;
                
        /*
        for (var b=0; b<NUM_BUTTONS; b++)
        {
            if ( b == 0  ) { xx = BUTTON_LEFT;      yy = BUTTON_TOP + h * 0; }
            if ( b == 1  ) { xx = BUTTON_LEFT + 90; yy = BUTTON_TOP + h * 0; }
            if ( b == 2  ) { xx = BUTTON_LEFT;      yy = BUTTON_TOP + h * 1; }
            if ( b == 3  ) { xx = BUTTON_LEFT + 90; yy = BUTTON_TOP + h * 1; }
            if ( b == 4  ) { xx = BUTTON_LEFT;      yy = BUTTON_TOP + h * 2; }
            if ( b == 5  ) { xx = BUTTON_LEFT + 90; yy = BUTTON_TOP + h * 2; }
            if ( b == 6  ) { xx = BUTTON_LEFT;      yy = BUTTON_TOP + h * 3; }
            if ( b == 7  ) { xx = BUTTON_LEFT + 90; yy = BUTTON_TOP + h * 3; }
    
            button[b] = new Button();
            button[b].x = xx;
            button[b].y = yy;
            button[b].w = BUTTON_WIDTH;
            button[b].h = BUTTON_HEIGHT;
            
            if (b ==  8 ) { button[b].x =   0; button[b].y = WINDOW_WIDTH * ROOT3_2 + 5; button[b].w = 200; button[b].h = 50; }
            if (b ==  9 ) { button[b].x = 200; button[b].y = WINDOW_WIDTH * ROOT3_2 + 5; button[b].w = 200; button[b].h = 50; }
            if (b == 10 ) { button[b].x = 400; button[b].y = WINDOW_WIDTH * ROOT3_2 + 5; button[b].w = 200; button[b].h = 50; }	
        }
        */
        
        var range = ( BUTTON_WIDTH + BUTTON_MARGIN ) * NUM_BUTTONS
        for (var b=0; b<NUM_BUTTONS; b++)
        {
            var frac = b / NUM_BUTTONS;
            button[b] = new Button();
            button[b].x = this.Xcenter - 300 - BUTTON_WIDTH / 2 + range * frac;
            button[b].y = WINDOW_HEIGHT + 30;
            button[b].w = BUTTON_WIDTH;
            button[b].h = BUTTON_HEIGHT;
        }	
	}
	
	
	
	
	//______________________________________________________________________________
    this.putIcosaPointsOnSphere = function()
	{
		var yy = 0.44721;
		var r = Math.cos( yy * Math.PI * 2.0 );

		for (var i=0; i<5; i++ )
		{
			var a = ( i / 5 ) * Math.PI * 2.0;

			var s = Math.sin(a) * r;
			var c = Math.cos(a) * r;

			this.cell[i].x  = s;
			this.cell[i].z  = c;
			this.cell[i].y  = -yy;

			this.cell[i+5].x  = c;
			this.cell[i+5].z  = s;
			this.cell[i+5].y  = yy;
		}

		this.cell[10].x =  0.0;
		this.cell[10].y = -1.0;
		this.cell[10].z =  0.0;

		this.cell[11].x =  0.0;
		this.cell[11].y =  1.0;
		this.cell[11].z =  0.0;

		//------------------------------------------------------------------
		// constrain points to sphere of size 1
		//------------------------------------------------------------------
		for (var c=0; c<NUM_ICOSA_POINTS; c++ )
		{
			var d2 =
			this.cell[c].x * this.cell[c].x + 
			this.cell[c].y * this.cell[c].y + 
			this.cell[c].z * this.cell[c].z;

			var dd = 1.0 / Math.sqrt(d2);

			this.cell[c].x *= dd;
			this.cell[c].y *= dd;
			this.cell[c].z *= dd;
		}
	}
	


	//______________________________________________________________________________
	this.geodesify = function()
	{
        //console.log( "" );
        //console.log( "" );
        //console.log( "" );
        //console.log( "" );
        //-------------------------------------------------
        // clear all neighbors
        //-------------------------------------------------
        console.log( "BEFORE clear all neighbors" );
        
        for (var c=0; c<this.numCells; c++)
        {
            for (var i=0; i<MAX_NEIGHBORS; i++)
            {
                this.cell[c].neighbor[i] = -1;
            }
        }
        console.log( "AFTER clear all neighbors" );
    
        //-------------------------------------------------
        // determine shortest distance between all cells
        //-------------------------------------------------
        var shortestDistance = this.findShortestDistance();
        
        //--------------------------------------------------------------------
        // find neighbors of each cell as cells which lie to within 
        // a little larger than average distance 
        //--------------------------------------------------------------------
        console.log( "BEFORE find neighbors" );
        
        for (var c=0; c<this.numCells; c++)
        {
            //console.log( "cell  " + c );        
            var numNeighbors = 6;
            
            if ( c < NUM_ICOSA_POINTS )
            {
                numNeighbors = 5;
            }
    
            var neighborIndex = 0;
    
            if ( neighborIndex < numNeighbors )
            {
                for (var cc=0; cc<this.numCells; cc++)
                {
                    if ( c != cc )
                    {
                        var xx = this.cell[c].x - this.cell[cc].x;
                        var yy = this.cell[c].y - this.cell[cc].y;
                        var zz = this.cell[c].z - this.cell[cc].z;
    
                        var distance = Math.sqrt( xx*xx + yy*yy + zz*zz );
                        if ( distance < shortestDistance * 1.6 )
                        {
                            this.cell[c].neighbor[ neighborIndex ] = cc;
                            //console.log( "     " + neighborIndex );        
                            neighborIndex ++;
                        }
                    }
                }
            }
        }
        console.log( "AFTER find neighbors" );
    
        //--------------------------------------------------------------------
        // important
        //--------------------------------------------------------------------
        var newCell = Math.floor( this.numCells - 1 );
    
        //--------------------------------------------------------------------
        // create new cells between all neighbors
        //--------------------------------------------------------------------
        console.log( "BEFORE create new cells between all neighbors:" );
        for (var c=0; c<this.numCells; c++)
        {
            if ( this.cell[c].initialized )
            {
                var numNeighbors = 6;
                if ( c < NUM_ICOSA_POINTS )
                {
                    numNeighbors = 5;
                }
    
                //--------------------------------------------------------------------
                // loop through neighbors
                //--------------------------------------------------------------------
                for (var n=0; n<numNeighbors; n++)
                {
                    //console.log( "neighbor " + n );
                    if ( this.numCells < MAX_CELLS )
                    {
                        var neighbor = this.cell[c].neighbor[n];

                        if ( neighbor == -1 ) 
                        {
                            console.log( "WARNING: neighbor = -1" );
                        }
    
                        if ( this.cell[ neighbor ].initialized )
                        {
                            //console.log( "neighbor " + neighbor + " is initialized" );
                        
                            if ( ! this.cell[c].birth[n] )
                            {
                                //console.log( "not born yet" );
                            
                                //---------------------------------------------------
                                // create the new cell 
                                //---------------------------------------------------
                                newCell ++;
                                this.cell[ newCell ].x = ( this.cell[c].x + this.cell[ neighbor ].x ) * ONE_HALF;
                                this.cell[ newCell ].y = ( this.cell[c].y + this.cell[ neighbor ].y ) * ONE_HALF;
                                this.cell[ newCell ].z = ( this.cell[c].z + this.cell[ neighbor ].z ) * ONE_HALF;
    
                                var distance = 
                                Math.sqrt
                                    ( 
                                        this.cell[ newCell ].x * this.cell[ newCell ].x + 
                                        this.cell[ newCell ].y * this.cell[ newCell ].y + 
                                        this.cell[ newCell ].z * this.cell[ newCell ].z 
                                    );
                                    
                                var dd = 1.0 / distance;
                                this.cell[ newCell ].x *= dd;
                                this.cell[ newCell ].y *= dd;
                                this.cell[ newCell ].z *= dd;
    
                                this.cell[ newCell ].initialized = false;
    
                                this.cell[c].neighbor[n] = newCell;
                                this.cell[c].birth	[n] = true;

                                //console.log( "neighbor " + n + " just born" );
    
                                //--------------------------------------------------
                                // tell neighbor that it has just had a new birth! 
                                //--------------------------------------------------
                                for (var nn=0; nn<numNeighbors; nn++)
                                {
                                    if ( this.cell[ neighbor ].neighbor[nn] == c )
                                    {
                                        this.cell[ neighbor ].neighbor	[nn] = newCell;
                                        this.cell[ neighbor ].birth		[nn] = true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        //--------------------------------------------------------------------
        // set the number of cells to the number of new cells + 1
        //--------------------------------------------------------------------
        this.numCells = Math.floor( newCell + 1 );

        //--------------------------------------------------------------------
        // now initialize all the cells
        //--------------------------------------------------------------------
        for (var c=0; c<this.numCells; c++)
        {
            this.cell[c].initialized = true;
        }
	}
	
	
	
	
	
	
	//____________________________________________________________________________________
	this.createRulesFromGenes = function( individual )
	{
		var g = 0;
		for (var s = 0; s < NUM_STATES; s++) 
		{
			ruleAge[s] = gene[ individual ][g]; g ++;
		}
		
		for (var r = 0; r < NUM_RULES; r++) 
		{
			ruleCell  [r] = gene[ individual ][g]; g ++;	
			ruleState [r] = gene[ individual ][g]; g ++;	
			ruleNum   [r] = gene[ individual ][g]; g ++;
			ruleResult[r] = gene[ individual ][g]; g ++;
		}
		
		if ( g != numGenesPerIndividual ) 
		{
			console.log( "hey, problem: numGenes is " + numGenesPerIndividual + " but I counted " + g );
		}		
	}
	
	


	//____________________________________________________________________________________
	this.printOutRules = function()
	{
		console.log( "rules:" );
		console.log( "" );

		for (var s = 0; s < NUM_STATES; s++) 
		{
			console.log( "ruleAge   [" + s + "] = " + ruleAge[s] + ";" );
		}
		
		for (var r = 0; r < NUM_RULES; r++) 
		{
			console.log
			(
				"ruleCell  [" + r + "] = " + ruleCell  [r] + ";  " + 
				"ruleState [" + r + "] = " + ruleState [r] + ";  " + 
				"ruleNum   [" + r + "] = " + ruleNum   [r] + ";  " +
				"ruleResult[" + r + "] = " + ruleResult[r] + ";"
			);
		}		

		console.log( "" );
	}
	


	//____________________________________________________________________________________
	this.randomizeCellStates = function()
	{
		for (var c=0; c<this.numCells; c++)
		{
			if ( Math.random() > 0.5 )
			{
				this.cell[c].state = Math.floor(Math.random() * NUM_STATES);				
			}
			else
			{
				this.cell[c].state = 0;				
			}
			
			//this.cell[c].backup = this.cell[c].state;
		}	
	}



	
	//____________________________________________________________________________________
	this.update = function()
	{	
        this.clock ++;
        
        if ( this.clock ==   1  ) { this.geodesify(); }
        if ( this.clock ==  60  ) { this.geodesify(); }
        if ( this.clock ==  90  ) { this.geodesify(); }
        if ( this.clock == 120  ) { this.geodesify(); }
        if ( this.clock == 150  ) { this.geodesify(); }
        if ( this.clock >  150  )
        {
            if ( ! neighborsFound )
            {
                this.findNeighbors();
                neighborsFound = true;
                
                /*
                for (var c=0; c<this.numCells; c++)
                {
                    var j = 0.01;
                    this.cell[c].x += -j * ONE_HALF + j * Math.random(); 
                    this.cell[c].y += -j * ONE_HALF + j * Math.random(); 
                    this.cell[c].z += -j * ONE_HALF + j * Math.random(); 
                }
                */
                
                this.randomizeCellStates();
            }
        }
        
        //---------------------------
        // render everything...
        //---------------------------
        this.render();

        //---------------------------------------------
        // save backup
        //---------------------------------------------
        for (var c=0; c<this.numCells; c++)
        {
            this.cell[c].backup = this.cell[c].state;				
        }
    
        //---------------------------------------------
        // apply rules
        //---------------------------------------------
        this.applyRules();
        
        //---------------------------------------------
        // stir it up!
        //---------------------------------------------
        if ( mouseIsDown )
        {
            //this.randomizeCellStates();
            this.stirItUp( mouseX, mouseY );
        }
        
        //---------------------------
        // rotate the world...
        //---------------------------
        rotation -= 0.002;		
        rotationSin = Math.sin( rotation );
        rotationCos = Math.cos( rotation );            

        //---------------------------
        // trigger next update...
        //---------------------------
        this.timer = setTimeout( "cells.update()", MILLISECONDS_PER_UPDATE );
	}
	

	//____________________________________________________________________________________
	this.findNeighbors = function()
	{
        var neighborDistanceThreshold = this.findShortestDistance() * 1.6;
	
        for (var c=0; c<this.numCells; c++)
        {
            var neighborIndex = 0;
    
            for (var cc=0; cc<this.numCells; cc++)
            {
                if ( c != cc )
                {
                    var xx = this.cell[c].x - this.cell[cc].x;
                    var yy = this.cell[c].y - this.cell[cc].y;
                    var zz = this.cell[c].z - this.cell[cc].z;
    
                    //--------------------------------
                    // get distance between cells
                    //--------------------------------
                    var d = xx*xx + yy*yy + zz*zz;
            
                    //---------------------------------------
                    // if close enough to be a neighbor
                    //---------------------------------------
                    var dd = neighborDistanceThreshold;
                    if ( d < dd * dd )
                    {
                        if ( neighborIndex < MAX_NEIGHBORS )
                        {
                            //--------------------------------
                            // add new neighbor
                            //--------------------------------
                            this.cell[c].neighbor[neighborIndex] = cc;
                            neighborIndex ++;
                            this.cell[c].numNeighbors = neighborIndex;
                        }
                    }
                }
            }
        }    
    }
    

	//____________________________________________________________________________________
	this.findShortestDistance = function()
	{	
	    var shortestDistance = 1000.0;
	    
        for (var c=0; c<this.numCells; c++)
        {
            for (var cc=0; cc<this.numCells; cc++)
            {
                if ( c != cc )
                {
                    var xx = this.cell[c].x - this.cell[cc].x;
                    var yy = this.cell[c].y - this.cell[cc].y;
                    var zz = this.cell[c].z - this.cell[cc].z;
    
                    var distance = Math.sqrt( xx*xx + yy*yy + zz*zz );
    
                    if ( distance < shortestDistance ) 
                    {
                        shortestDistance = distance;
                    }
                }
            }
        }
	   
	    return shortestDistance;
	}
	
	
	//____________________________________________________________________________________
	this.applyRules = function()
	{
		for (var c=0; c<this.numCells; c++)
		{            
            //-----------------------------------
            // determine neighbor counts
            //-----------------------------------
            for (var s=0; s<NUM_STATES; s++)
            {
                num[s] = 0;
            }

            for (var n=0; n<this.cell[c].numNeighbors; n++)
            {
                num[ this.cell[ this.cell[c].neighbor[n] ].backup ] ++;
            }
            
            if ( this.cell[c].age < ruleAge[ this.cell[c].backup ] )
            {
                this.cell[c].age ++;
                this.cell[c].state = this.cell[c].backup;
            }
            else
            {
                this.cell[c].state = 0;
            }
                            
            //-----------------------------------
            // apply transition rules
            //-----------------------------------							
            for (var r = 0; r < NUM_RULES; r++) 
            {
                if ( this.cell[c].backup == ruleCell[r] )
                {
                    //console.log( ruleState[r] );
                    //console.log( num[ ruleState[r] ] + ", " + ruleNum[r] );

                    if ( num[ ruleState[r] ] == ruleNum[r] )
                    {
                        this.cell[c].state = ruleResult[r];
                        this.cell[c].age = 0;
                    }
                }
            }				
        }
    }





	//____________________________________________________________________________________
	this.render = function()
	{
		//-------------------------------------------
		// clear the screen
		//-------------------------------------------
		canvas.clearRect( 0, 0, document.body.clientWidth, WINDOW_HEIGHT );

		//-------------------------------------------
		// draw the earth sphere
		//-------------------------------------------
        if ( neighborsFound )
        {
            var radius = 242;
            canvas.drawImage( this.earthImage, this.Xcenter - radius, WINDOW_HEIGHT / 2 - radius );		
        }
		
		//-------------------------------------------
		// draw the cells
		//-------------------------------------------
		for (var c=0; c<this.numCells; c++)
		{
		    var rotatedZ = this.cell[c].z * rotationSin - this.cell[c].x * rotationCos;

            if ( rotatedZ > 0.0 )
            {
                var rotatedX = this.cell[c].x * rotationSin + this.cell[c].z * rotationCos;
    
                var x = this.Xcenter + rotatedX * SCALE - 2;
                var y = WINDOW_HEIGHT / 2 + this.cell[c].y * SCALE;
                    
                //-----------------------------------------------------------
                // find the right shading for the cell, and draw it
                //-----------------------------------------------------------
                var ss = Math.floor( rotatedZ * NUM_STATES * 0.6 + rotatedX * NUM_STATES * 0.6 );
                if ( ss < 0 )
                {
                    ss = 0;
                }
                if ( ss > NUM_STATES - 1 )
                {
                    ss = NUM_STATES - 1;
                }
                
                if ( this.cell[c].state == 0 )
                {
                    if ( ! neighborsFound )
		            {
                        var ss = 0.5 + rotatedX * ONE_HALF;
                        var r = Math.floor(  50 * ss );
                        var g = Math.floor( 100 * ss );
                        var b = Math.floor( 150 * ss );
                        canvas.fillStyle = "rgb(" + r + "," + g + "," + b +  ")";

                        canvas.fillRect( x + CELL_SIZE * 0.25,  y,                      CELL_SIZE * 0.5, CELL_SIZE * 0.25 );
                        canvas.fillRect( x,                     y + CELL_SIZE * 0.25,   CELL_SIZE * 1.0, CELL_SIZE * 0.50 );
                        canvas.fillRect( x + CELL_SIZE * 0.25,  y + CELL_SIZE * 0.75,   CELL_SIZE * 0.5, CELL_SIZE * 0.25 );
                    }
                }
                else
                {
                    canvas.fillStyle = color[ this.cell[c].state ];
                    //canvas.fillRect( x, y, CELL_SIZE, CELL_SIZE );

                    //canvas.fillRect( x + CELL_SIZE * 0.25,  y,                      CELL_SIZE * 0.5, CELL_SIZE * 0.25 );
                    //canvas.fillRect( x,                     y + CELL_SIZE * 0.25,   CELL_SIZE * 1.0, CELL_SIZE * 0.50 );
                    //canvas.fillRect( x + CELL_SIZE * 0.25,  y + CELL_SIZE * 0.75,   CELL_SIZE * 0.5, CELL_SIZE * 0.25 );


        

canvas.beginPath();
canvas.moveTo( x,                   y - CELL_SIZE * 0.5 );
canvas.lineTo( x + CELL_SIZE * 0.45, y - CELL_SIZE * 0.25 );
canvas.lineTo( x + CELL_SIZE * 0.45, y + CELL_SIZE * 0.25 );
canvas.lineTo( x,                   y + CELL_SIZE * 0.5 );
canvas.lineTo( x - CELL_SIZE * 0.45, y + CELL_SIZE * 0.25 );
canvas.lineTo( x - CELL_SIZE * 0.45, y - CELL_SIZE * 0.25 );
canvas.lineTo( x,                   y - CELL_SIZE * 0.5 );
canvas.closePath();
canvas.fill();      


                }
            }
		}
		
		//-------------------------------------------
		// show message for geodesifying....
		//-------------------------------------------
		if ( ! neighborsFound )
		{
            canvas.fillStyle = "rgb( 180, 180, 180 )";
		    canvas.fillText  ( "Building Earth (please wait 7 days)",	document.body.clientWidth / 2 - 120, WINDOW_HEIGHT /2 );
		}
    
		//-------------------------------------------
		// draw a frame around everything....
		//-------------------------------------------
		//canvas.lineWidth = 2; 		
		//canvas.strokeStyle = "rgb( 130, 130, 130 )"; 		
		//canvas.strokeRect( 1, 1, WINDOW_WIDTH, WINDOW_HEIGHT - 2 );
	}
	




	//____________________________________________________________________________________
	this.renderPopulation = function()
	{
		var left 		= 820;
		var top 		= 550;
		var width	 	= 320;
		var height	 	= 90;
		var thickness 	= 2;
		var geneWidth	= width  / NUM_INDIVIDUALS;
		var geneHeight	= height / numGenesPerIndividual;
		
		//---------------------------------------
		// backgrounds behind various elements
		//---------------------------------------
		canvas.fillStyle = "rgb( 51, 51, 51 )"; 			
		canvas.fillRect
		( 
			left, 
			top - height,
			width + 100, 
			height + 130
		);

				
		//---------------------------------------
		// text elements
		//---------------------------------------
		canvas.fillStyle = "rgb( 130, 130, 130 )";
		canvas.fillText  ( 'fitness',   left + width + 10, top + height - 20 );
		canvas.fillText  ( parent1,  			left + 2 + (parent1				/NUM_INDIVIDUALS) * (width - 4), top - 25 );
		canvas.fillText  ( parent2,  			left + 2 + (parent2				/NUM_INDIVIDUALS) * (width - 4), top - 25 );
		canvas.fillText  ( currentIndividual,  	left + 2 + (currentIndividual	/NUM_INDIVIDUALS) * (width - 4), top - 25 );


		//---------------------------------------
		// parent1, parent2, offspring
		//---------------------------------------
		canvas.fillStyle = "rgb( 222, 100, 100 )"; 			
		canvas.fillRect 
		( 
			left + 2 + (parent1/NUM_INDIVIDUALS) * (width - 4), 
			top  - 5,
			geneWidth, 
			5 
		);
		canvas.fillStyle = "rgb( 100, 180, 255 )"; 			
		canvas.fillRect 
		( 
			left + 2 + (parent2/NUM_INDIVIDUALS) * (width - 4), 
			top - 5,
			geneWidth, 
			5 
		);

		canvas.fillStyle = "rgb( 222, 222, 100 )"; 			
		canvas.fillRect 
		( 
			left + 2 + (currentIndividual/NUM_INDIVIDUALS) * (width - 4), 
			top - 5,
			geneWidth, 
			5 
		);


		//---------------------------------------
		// lexicon for parents and offspring
		//---------------------------------------
		var t = top + height + 20;
		var s = 90;
		
		canvas.fillStyle = "rgb( 222, 100, 100 )"; 			
		canvas.fillRect( left, t, geneWidth, 5 );

		canvas.fillStyle = "rgb( 100, 180, 255 )"; 			
		canvas.fillRect( left + s, t, geneWidth, 5 );

		canvas.fillStyle = "rgb( 222, 222, 100 )"; 			
		canvas.fillRect( left + s*2, t, geneWidth, 5 );

		canvas.fillStyle = "rgb( 130, 130, 130 )";
		canvas.fillText  ( "parent 1",	left + 10, t - 8 );
		canvas.fillText  ( "parent 2",	left + 10 + s, t - 8 );
		canvas.fillText  ( "offspring",	left + 10 + s * 2, t - 8 );


		
		//---------------------------------------
		// fitness graph background
		//---------------------------------------
		canvas.fillStyle = "rgb( 100, 100, 100 )";
		canvas.fillRect( left, top, width, height );
		
		for (var i = 0; i < NUM_INDIVIDUALS; i++) 
		{	
			var x = left + 2 + (i/NUM_INDIVIDUALS) * (width - 4);

			//---------------------------------------
			// fitness
			//---------------------------------------
			canvas.fillStyle = "rgb( 150, 150, 150 )"; 			
			canvas.fillRect
			( 
				x + geneWidth / 2, 
				top + height,
				thickness, 
				-fitness[i] * ( height - 2 ) 
			);
		}	
	}
	
	
	

	//____________________________________________________________________________________
    this.renderButton = function( b, highlight )
	{
		if ( highlight )
		{
			canvas.fillStyle 	= "rgba( 90, 90, 90, 255 )"; 			
			canvas.strokeStyle 	= "rgba( 190, 200, 220, 255 )"; 			
		}
		else
		{
			canvas.fillStyle 	= "rgba( 70, 70, 70, 255 )"; 			
			canvas.strokeStyle 	= "rgba( 120, 140, 160, 255 )"; 			
		}

		canvas.fillRect  ( button[b].x, button[b].y, button[b].w, button[b].h );
		canvas.strokeRect( button[b].x, button[b].y, button[b].w, button[b].h );
		
		canvas.fillStyle = "rgba( 150, 160, 180, 255 )"; 
		canvas.font         = '15px sans-serif';
		canvas.textBaseline = 'top';
		
		if ( b ==  0 ) {	canvas.fillText  ('Growth', 	button[b].x + 5, button[b].y + 5 ); }
		if ( b ==  1 ) {	canvas.fillText  ('Migrate',   	button[b].x + 5, button[b].y + 5 ); }
		if ( b ==  2 ) {	canvas.fillText  ('Tidal', 	    button[b].x + 5, button[b].y + 5 ); }
		if ( b ==  3 ) {	canvas.fillText  ('Life ',  	button[b].x + 5, button[b].y + 5 ); }

		if ( b ==  4 ) {	canvas.fillText  ('Wiggle',	    button[b].x + 5, button[b].y + 5 ); }
		if ( b ==  5 ) {	canvas.fillText  ('Islands',  	button[b].x + 5, button[b].y + 5 ); }
		if ( b ==  6 ) {	canvas.fillText  ('Replicate', 	button[b].x + 5, button[b].y + 5 ); }
		if ( b ==  7 ) {	canvas.fillText  ('Storms',     button[b].x + 5, button[b].y + 5 ); }
		
		if ( b ==  8 ) {	canvas.fillText  ('bad', 		button[b].x + 5, button[b].y + 5 ); }
		if ( b ==  9 ) {	canvas.fillText  ('ok', 		button[b].x + 5, button[b].y + 5 ); }
		if ( b == 10 ) {	canvas.fillText  ('good', 		button[b].x + 5, button[b].y + 5 ); }	
	}
	



	
	//____________________________________________________________________________________
	this.mouseDown = function( x, y )
	{		
		mouseIsDown = true;
	
		mouseX = x;
		mouseY = y;
		
		for (var b=0; b<NUM_BUTTONS; b++)
		{
			if (( mouseX > button[b].x + MOUSE_FUDGE_SHIFT )
			&&  ( mouseX < button[b].x + MOUSE_FUDGE_SHIFT + button[b].w )
			&&  ( mouseY > button[b].y + MOUSE_FUDGE_SHIFT )
			&&  ( mouseY < button[b].y + MOUSE_FUDGE_SHIFT + button[b].h ))
			{
				this.chooseButton( b );
			}
		}
	}
	
	//____________________________________________________________________________________
	this.stirItUp = function( x, y )
	{
        var range  = 0.1;
        var Xthing = 4.7;
        var Ything = 2.3;
        
        x = -Xthing * ONE_HALF + ( x / document.body.clientWidth  ) * Xthing;
        y = -Ything * ONE_HALF + ( y / WINDOW_HEIGHT              ) * Ything;
        
        for (var c=0; c<this.numCells; c++)
        {
            var rotatedZ = this.cell[c].z * rotationSin - this.cell[c].x * rotationCos;
    
            if ( rotatedZ > 0.0 )
            {
                var rotatedX = this.cell[c].x * rotationSin + this.cell[c].z * rotationCos;
    
                //var x = WINDOW_WIDTH  / 2 + rotatedX * SCALE - 2;
                //var y = WINDOW_HEIGHT / 2 + this.cell[c].y * SCALE;	
            
                if (( x < rotatedX + range )
                &&  ( x > rotatedX - range )
                &&  ( y < this.cell[c].y + range )
                &&  ( y > this.cell[c].y - range ))
                {
                    this.cell[c].state = 1 + Math.floor( Math.random() * ( NUM_STATES - 1 ) );
                }
            }
        }
	}
	

	
	
	
	//____________________________________________________________________________________
	this.chooseButton = function(b)
	{		
	    /*
				if (b ==  8 ) { this.setFitness( currentIndividual, 0.0 ); this.updatePopulation(); }
		else	if (b ==  9 ) { this.setFitness( currentIndividual, 0.5 ); this.updatePopulation(); }
		else	if (b == 10 ) { this.setFitness( currentIndividual, 1.0 ); this.updatePopulation(); this.decayFitness(); }
		else
		*/
		
		{

/*
if ( b == 7 )
{
    this.printOutRules();
}
else
*/
{
			this.loadPresetRules( b ); 
			this.randomizeCellStates(); 	
}
		}	
		
		//-------------------------------------------
		// render population....
		//-------------------------------------------
		//this.renderPopulation();		
	}
	



	//____________________________________________________________________________________
	this.addFitness = function( individual, amount )
	{		
		fitness[ individual ] += amount;
		
		if ( fitness[ individual ] < 0.0 )
		{
			fitness[ individual ] = 0.0;
		}
		else if ( fitness[ individual ] > 1.0 )
		{
			fitness[ individual ] = 1.0;
		}
	}
	
	//____________________________________________________________________________________
	this.setFitness = function( individual, f )
	{		
		fitness[ individual ] = f;
	}
	


	//____________________________________________________________________________________
	this.updatePopulation = function()
	{		
		parent1 = this.findRelativelyFitIndividual();
		parent2 = this.findRelativelyFitIndividual();
		
		currentIndividual = this.mate(); 
		
		this.createRulesFromGenes( currentIndividual );			
		this.randomizeCellStates(); 
	}
	
	

	//____________________________________________________________________________________
	this.decayFitness = function()
	{		
		for (var i = 0; i < NUM_INDIVIDUALS; i++) 
		{
			fitness[i] *= FITNESS_DECAY;
		}
	}	
	


	//____________________________________________________________________________________
	this.findRelativelyFitIndividual = function()
	{		
		var test1 = Math.floor( Math.random() * NUM_INDIVIDUALS );	
		var test2 = Math.floor( Math.random() * NUM_INDIVIDUALS );	
		
		//console.log( "test1 = " + test1 );
		//console.log( "test2 = " + test2 );

		//console.log( "fitness of test1 = " + fitness[ test1 ] );
		//console.log( "fitness of test2 = " + fitness[ test2 ] );
		
		if ( fitness[ test1 ] > fitness[ test2 ] )
		{
			//console.log( "choosing " + test1 );
			return test1;
		}
		else
		{
			//console.log( "choosing " + test2 );
		}
		
		return test2;	
	}




	//____________________________________________________________________________________
	this.mate = function()
	{		
		var offspring = this.findLeastFitIndividual();
		var parent = parent1;
		
		var g = 0;
		for (var s = 0; s < NUM_STATES; s++) 
		{
			if ( Math.random() < CROSSOVER_RATE )
			{
				if ( parent == parent1 )
				{
					parent = parent2;
				}
				else
				{
					parent = parent1;
				}
			}

			gene[ offspring ][g] = gene[ parent ][g]; g++;

			if ( Math.random() < MUTATION_RATE ) 
			{
				gene[ offspring ][g] = Math.floor( Math.random() * MAX_AGE ); // ruleAge 
			}
		}

		for (var r = 0; r < NUM_RULES; r++) 
		{
			for (var e = 0; e < NUM_RULE_ELEMENTS; e++) 
			{
				if ( Math.random() < CROSSOVER_RATE )
				{
					if ( parent == parent1 )
					{
						parent = parent2;
					}
					else
					{
						parent = parent1;
					}
				}

				gene[ offspring ][g] = gene[ parent ][g]; g++;				
	
				if ( Math.random() < MUTATION_RATE ) 
				{
					if ( e == 0 ) { gene[ offspring ][g] =     Math.floor( Math.random() * (NUM_STATES  )		); } // ruleCell
					if ( e == 1 ) { gene[ offspring ][g] = 1 + Math.floor( Math.random() * (NUM_STATES-1)    	); } // ruleState
					if ( e == 2 ) { gene[ offspring ][g] = 1 + Math.floor( Math.random() * MAX_NEIGHBOR_COUNT	); } // ruleNum
					if ( e == 3 ) { gene[ offspring ][g] =     Math.floor( Math.random() * (NUM_STATES  )		); } // ruleResult
				}
			}
		}
		
		if ( g != numGenesPerIndividual ) 
		{
			console.log( "hey, problem: numGenes is " + numGenesPerIndividual + " but I counted " + g );
		}
		
		return offspring;
	}





	//____________________________________________________________________________________
	this.findLeastFitIndividual = function()
	{		
		var leastFit = 0;
		var lowestFitness = 10000.0;
		
		for (var i = 0; i < NUM_INDIVIDUALS; i++) 
		{
			if ( fitness[i] < lowestFitness )
			{
				lowestFitness = fitness[i];
				leastFit = i;
			}
		}
	
		return leastFit;
	}




	//____________________________________________________________________________________
	this.mouseMove = function( x, y )
	{		
		mouseX = x;
		mouseY = y;
		
//for (var b=0; b<NUM_BUTTONS; b++)
for (var b=0; b<8; b++)
		{
			if (( mouseX > button[b].x + MOUSE_FUDGE_SHIFT )
			&&  ( mouseX < button[b].x + MOUSE_FUDGE_SHIFT + button[b].w )
			&&  ( mouseY > button[b].y + MOUSE_FUDGE_SHIFT )
			&&  ( mouseY < button[b].y + MOUSE_FUDGE_SHIFT + button[b].h ))
			{
				this.renderButton( b, true);
			}
			else
			{
				this.renderButton( b, false);
			}
		}	 
	}
	



	//____________________________________________________________________________________
	this.mouseUp = function( x, y )
	{
		mouseIsDown = false;
		mouseX = x;
		mouseY = y;
	}
	
	
	




	//____________________________________________________________________________________
	this.loadPresetRules = function(p)
	{		
		if (p == 0 )
		{
		    // growth
			ruleAge   [0] = 2;
			ruleAge   [1] = 1;
			ruleAge   [2] = 1;
			ruleAge   [3] = 2;
			ruleAge   [4] = 1;
			ruleAge   [5] = 0;
			ruleAge   [6] = 0;
			ruleCell  [0] = 4;  ruleState [0] = 5;  ruleNum   [0] = 1;  ruleResult[0] = 4;
			ruleCell  [1] = 4;  ruleState [1] = 1;  ruleNum   [1] = 1;  ruleResult[1] = 2;
			ruleCell  [2] = 2;  ruleState [2] = 3;  ruleNum   [2] = 1;  ruleResult[2] = 1;
			ruleCell  [3] = 0;  ruleState [3] = 6;  ruleNum   [3] = 2;  ruleResult[3] = 0;
			ruleCell  [4] = 4;  ruleState [4] = 6;  ruleNum   [4] = 2;  ruleResult[4] = 6;
			ruleCell  [5] = 0;  ruleState [5] = 2;  ruleNum   [5] = 2;  ruleResult[5] = 2;
			ruleCell  [6] = 6;  ruleState [6] = 5;  ruleNum   [6] = 2;  ruleResult[6] = 3;
			ruleCell  [7] = 0;  ruleState [7] = 2;  ruleNum   [7] = 3;  ruleResult[7] = 2;
			ruleCell  [8] = 2;  ruleState [8] = 5;  ruleNum   [8] = 3;  ruleResult[8] = 4;
			ruleCell  [9] = 2;  ruleState [9] = 3;  ruleNum   [9] = 3;  ruleResult[9] = 1;
			ruleCell  [10] = 0;  ruleState [10] = 1;  ruleNum   [10] = 3;  ruleResult[10] = 6;
			ruleCell  [11] = 2;  ruleState [11] = 6;  ruleNum   [11] = 3;  ruleResult[11] = 4;
			ruleCell  [12] = 5;  ruleState [12] = 1;  ruleNum   [12] = 2;  ruleResult[12] = 5;
			ruleCell  [13] = 1;  ruleState [13] = 4;  ruleNum   [13] = 2;  ruleResult[13] = 2;
			ruleCell  [14] = 3;  ruleState [14] = 4;  ruleNum   [14] = 2;  ruleResult[14] = 4;
			ruleCell  [15] = 3;  ruleState [15] = 5;  ruleNum   [15] = 1;  ruleResult[15] = 4;
			ruleCell  [16] = 2;  ruleState [16] = 5;  ruleNum   [16] = 3;  ruleResult[16] = 6;
			ruleCell  [17] = 0;  ruleState [17] = 2;  ruleNum   [17] = 3;  ruleResult[17] = 4;
			ruleCell  [18] = 1;  ruleState [18] = 4;  ruleNum   [18] = 2;  ruleResult[18] = 2;
			ruleCell  [19] = 2;  ruleState [19] = 6;  ruleNum   [19] = 1;  ruleResult[19] = 2;
			ruleCell  [20] = 1;  ruleState [20] = 3;  ruleNum   [20] = 2;  ruleResult[20] = 5;
			ruleCell  [21] = 6;  ruleState [21] = 4;  ruleNum   [21] = 1;  ruleResult[21] = 2;
			ruleCell  [22] = 3;  ruleState [22] = 5;  ruleNum   [22] = 1;  ruleResult[22] = 2;
			ruleCell  [23] = 6;  ruleState [23] = 1;  ruleNum   [23] = 2;  ruleResult[23] = 3;
			ruleCell  [24] = 4;  ruleState [24] = 2;  ruleNum   [24] = 2;  ruleResult[24] = 2;
			ruleCell  [25] = 2;  ruleState [25] = 2;  ruleNum   [25] = 1;  ruleResult[25] = 0;
			ruleCell  [26] = 5;  ruleState [26] = 1;  ruleNum   [26] = 1;  ruleResult[26] = 3;
			ruleCell  [27] = 2;  ruleState [27] = 3;  ruleNum   [27] = 3;  ruleResult[27] = 4;
			ruleCell  [28] = 4;  ruleState [28] = 1;  ruleNum   [28] = 2;  ruleResult[28] = 2;
			ruleCell  [29] = 6;  ruleState [29] = 2;  ruleNum   [29] = 2;  ruleResult[29] = 0;
			ruleCell  [30] = 4;  ruleState [30] = 6;  ruleNum   [30] = 1;  ruleResult[30] = 1;
			ruleCell  [31] = 3;  ruleState [31] = 1;  ruleNum   [31] = 2;  ruleResult[31] = 5;
			ruleCell  [32] = 3;  ruleState [32] = 5;  ruleNum   [32] = 1;  ruleResult[32] = 3;
			ruleCell  [33] = 6;  ruleState [33] = 4;  ruleNum   [33] = 3;  ruleResult[33] = 0;
			ruleCell  [34] = 4;  ruleState [34] = 3;  ruleNum   [34] = 3;  ruleResult[34] = 5;
			ruleCell  [35] = 3;  ruleState [35] = 6;  ruleNum   [35] = 3;  ruleResult[35] = 5;
			ruleCell  [36] = 2;  ruleState [36] = 1;  ruleNum   [36] = 1;  ruleResult[36] = 1;
			ruleCell  [37] = 0;  ruleState [37] = 4;  ruleNum   [37] = 3;  ruleResult[37] = 4;
			ruleCell  [38] = 1;  ruleState [38] = 5;  ruleNum   [38] = 1;  ruleResult[38] = 5;
			ruleCell  [39] = 1;  ruleState [39] = 5;  ruleNum   [39] = 3;  ruleResult[39] = 3;		
		}
		else if (p == 1 )
		{
            // migrate
			ruleAge   [0] = 2;
			ruleAge   [1] = 1;
			ruleAge   [2] = 1;
			ruleAge   [3] = 1;
			ruleAge   [4] = 1;
			ruleAge   [5] = 0;
			ruleAge   [6] = 0;
			ruleCell  [0] = 3;  ruleState [0] = 1;  ruleNum   [0] = 3;  ruleResult[0] = 2;
			ruleCell  [1] = 0;  ruleState [1] = 2;  ruleNum   [1] = 2;  ruleResult[1] = 0;
			ruleCell  [2] = 6;  ruleState [2] = 6;  ruleNum   [2] = 3;  ruleResult[2] = 5;
			ruleCell  [3] = 3;  ruleState [3] = 6;  ruleNum   [3] = 1;  ruleResult[3] = 1;
			ruleCell  [4] = 6;  ruleState [4] = 4;  ruleNum   [4] = 3;  ruleResult[4] = 0;
			ruleCell  [5] = 0;  ruleState [5] = 4;  ruleNum   [5] = 3;  ruleResult[5] = 1;
			ruleCell  [6] = 0;  ruleState [6] = 5;  ruleNum   [6] = 3;  ruleResult[6] = 1;
			ruleCell  [7] = 6;  ruleState [7] = 6;  ruleNum   [7] = 1;  ruleResult[7] = 5;
			ruleCell  [8] = 0;  ruleState [8] = 6;  ruleNum   [8] = 3;  ruleResult[8] = 5;
			ruleCell  [9] = 6;  ruleState [9] = 3;  ruleNum   [9] = 2;  ruleResult[9] = 5;
			ruleCell  [10] = 0;  ruleState [10] = 1;  ruleNum   [10] = 2;  ruleResult[10] = 1;
			ruleCell  [11] = 1;  ruleState [11] = 1;  ruleNum   [11] = 1;  ruleResult[11] = 4;
			ruleCell  [12] = 5;  ruleState [12] = 3;  ruleNum   [12] = 1;  ruleResult[12] = 6;
			ruleCell  [13] = 3;  ruleState [13] = 2;  ruleNum   [13] = 2;  ruleResult[13] = 4;
			ruleCell  [14] = 0;  ruleState [14] = 2;  ruleNum   [14] = 1;  ruleResult[14] = 0;
			ruleCell  [15] = 3;  ruleState [15] = 2;  ruleNum   [15] = 2;  ruleResult[15] = 5;
			ruleCell  [16] = 0;  ruleState [16] = 3;  ruleNum   [16] = 1;  ruleResult[16] = 0;
			ruleCell  [17] = 1;  ruleState [17] = 3;  ruleNum   [17] = 3;  ruleResult[17] = 0;
			ruleCell  [18] = 5;  ruleState [18] = 4;  ruleNum   [18] = 1;  ruleResult[18] = 3;
			ruleCell  [19] = 1;  ruleState [19] = 4;  ruleNum   [19] = 3;  ruleResult[19] = 4;
			ruleCell  [20] = 6;  ruleState [20] = 2;  ruleNum   [20] = 1;  ruleResult[20] = 1;
			ruleCell  [21] = 3;  ruleState [21] = 2;  ruleNum   [21] = 1;  ruleResult[21] = 0;
			ruleCell  [22] = 6;  ruleState [22] = 4;  ruleNum   [22] = 3;  ruleResult[22] = 0;
			ruleCell  [23] = 2;  ruleState [23] = 4;  ruleNum   [23] = 1;  ruleResult[23] = 5;
			ruleCell  [24] = 1;  ruleState [24] = 1;  ruleNum   [24] = 2;  ruleResult[24] = 5;
			ruleCell  [25] = 0;  ruleState [25] = 3;  ruleNum   [25] = 3;  ruleResult[25] = 6;
			ruleCell  [26] = 2;  ruleState [26] = 4;  ruleNum   [26] = 1;  ruleResult[26] = 1;
			ruleCell  [27] = 4;  ruleState [27] = 6;  ruleNum   [27] = 2;  ruleResult[27] = 1;
			ruleCell  [28] = 4;  ruleState [28] = 1;  ruleNum   [28] = 1;  ruleResult[28] = 2;
			ruleCell  [29] = 5;  ruleState [29] = 3;  ruleNum   [29] = 3;  ruleResult[29] = 6;
			ruleCell  [30] = 5;  ruleState [30] = 3;  ruleNum   [30] = 1;  ruleResult[30] = 6;
			ruleCell  [31] = 0;  ruleState [31] = 2;  ruleNum   [31] = 3;  ruleResult[31] = 2;
			ruleCell  [32] = 6;  ruleState [32] = 2;  ruleNum   [32] = 2;  ruleResult[32] = 5;
			ruleCell  [33] = 5;  ruleState [33] = 3;  ruleNum   [33] = 2;  ruleResult[33] = 2;
			ruleCell  [34] = 6;  ruleState [34] = 4;  ruleNum   [34] = 3;  ruleResult[34] = 1;
			ruleCell  [35] = 0;  ruleState [35] = 4;  ruleNum   [35] = 2;  ruleResult[35] = 0;
			ruleCell  [36] = 4;  ruleState [36] = 6;  ruleNum   [36] = 2;  ruleResult[36] = 6;
			ruleCell  [37] = 4;  ruleState [37] = 3;  ruleNum   [37] = 3;  ruleResult[37] = 5;
			ruleCell  [38] = 1;  ruleState [38] = 3;  ruleNum   [38] = 1;  ruleResult[38] = 2;
			ruleCell  [39] = 0;  ruleState [39] = 6;  ruleNum   [39] = 3;  ruleResult[39] = 1;
		}
		else if (p == 2 )
		{
		    // tidal
            ruleAge   [0] = 1;
            ruleAge   [1] = 1;
            ruleAge   [2] = 0;
            ruleAge   [3] = 2;
            ruleAge   [4] = 1;
            ruleAge   [5] = 0;
            ruleAge   [6] = 2;
            ruleCell  [0] = 2;  ruleState [0] = 3;  ruleNum   [0] = 1;  ruleResult[0] = 6;
            ruleCell  [1] = 0;  ruleState [1] = 4;  ruleNum   [1] = 2;  ruleResult[1] = 4;
            ruleCell  [2] = 1;  ruleState [2] = 4;  ruleNum   [2] = 1;  ruleResult[2] = 3;
            ruleCell  [3] = 6;  ruleState [3] = 5;  ruleNum   [3] = 1;  ruleResult[3] = 6;
            ruleCell  [4] = 0;  ruleState [4] = 5;  ruleNum   [4] = 3;  ruleResult[4] = 5;
            ruleCell  [5] = 3;  ruleState [5] = 3;  ruleNum   [5] = 3;  ruleResult[5] = 2;
            ruleCell  [6] = 6;  ruleState [6] = 2;  ruleNum   [6] = 1;  ruleResult[6] = 1;
            ruleCell  [7] = 0;  ruleState [7] = 3;  ruleNum   [7] = 2;  ruleResult[7] = 4;
            ruleCell  [8] = 5;  ruleState [8] = 3;  ruleNum   [8] = 2;  ruleResult[8] = 6;
            ruleCell  [9] = 4;  ruleState [9] = 5;  ruleNum   [9] = 1;  ruleResult[9] = 2;
            ruleCell  [10] = 0;  ruleState [10] = 3;  ruleNum   [10] = 3;  ruleResult[10] = 0;
            ruleCell  [11] = 5;  ruleState [11] = 1;  ruleNum   [11] = 1;  ruleResult[11] = 0;
            ruleCell  [12] = 2;  ruleState [12] = 5;  ruleNum   [12] = 3;  ruleResult[12] = 3;
            ruleCell  [13] = 5;  ruleState [13] = 5;  ruleNum   [13] = 1;  ruleResult[13] = 1;
            ruleCell  [14] = 0;  ruleState [14] = 6;  ruleNum   [14] = 1;  ruleResult[14] = 1;
            ruleCell  [15] = 5;  ruleState [15] = 1;  ruleNum   [15] = 2;  ruleResult[15] = 4;
            ruleCell  [16] = 0;  ruleState [16] = 6;  ruleNum   [16] = 2;  ruleResult[16] = 2;
            ruleCell  [17] = 1;  ruleState [17] = 4;  ruleNum   [17] = 3;  ruleResult[17] = 5;
            ruleCell  [18] = 2;  ruleState [18] = 2;  ruleNum   [18] = 2;  ruleResult[18] = 5;
            ruleCell  [19] = 4;  ruleState [19] = 6;  ruleNum   [19] = 1;  ruleResult[19] = 6;
            ruleCell  [20] = 6;  ruleState [20] = 2;  ruleNum   [20] = 1;  ruleResult[20] = 4;
            ruleCell  [21] = 1;  ruleState [21] = 3;  ruleNum   [21] = 3;  ruleResult[21] = 3;
            ruleCell  [22] = 2;  ruleState [22] = 4;  ruleNum   [22] = 1;  ruleResult[22] = 2;
            ruleCell  [23] = 6;  ruleState [23] = 6;  ruleNum   [23] = 2;  ruleResult[23] = 4;
            ruleCell  [24] = 5;  ruleState [24] = 6;  ruleNum   [24] = 3;  ruleResult[24] = 2;
            ruleCell  [25] = 5;  ruleState [25] = 4;  ruleNum   [25] = 2;  ruleResult[25] = 2;
            ruleCell  [26] = 0;  ruleState [26] = 6;  ruleNum   [26] = 1;  ruleResult[26] = 2;
            ruleCell  [27] = 1;  ruleState [27] = 2;  ruleNum   [27] = 3;  ruleResult[27] = 5;
            ruleCell  [28] = 4;  ruleState [28] = 1;  ruleNum   [28] = 1;  ruleResult[28] = 1;
            ruleCell  [29] = 2;  ruleState [29] = 5;  ruleNum   [29] = 3;  ruleResult[29] = 6;
            ruleCell  [30] = 5;  ruleState [30] = 5;  ruleNum   [30] = 3;  ruleResult[30] = 0;
            ruleCell  [31] = 3;  ruleState [31] = 2;  ruleNum   [31] = 3;  ruleResult[31] = 4;
            ruleCell  [32] = 1;  ruleState [32] = 3;  ruleNum   [32] = 2;  ruleResult[32] = 0;
            ruleCell  [33] = 2;  ruleState [33] = 4;  ruleNum   [33] = 1;  ruleResult[33] = 5;
            ruleCell  [34] = 0;  ruleState [34] = 4;  ruleNum   [34] = 3;  ruleResult[34] = 0;
            ruleCell  [35] = 3;  ruleState [35] = 6;  ruleNum   [35] = 3;  ruleResult[35] = 1;
            ruleCell  [36] = 3;  ruleState [36] = 4;  ruleNum   [36] = 2;  ruleResult[36] = 2;
            ruleCell  [37] = 6;  ruleState [37] = 2;  ruleNum   [37] = 1;  ruleResult[37] = 6;
            ruleCell  [38] = 6;  ruleState [38] = 4;  ruleNum   [38] = 2;  ruleResult[38] = 1;
            ruleCell  [39] = 5;  ruleState [39] = 6;  ruleNum   [39] = 2;  ruleResult[39] = 1;
		}
		else if (p == 3 )
		{
		    // life
            ruleAge   [0] = 2;
            ruleAge   [1] = 1;
            ruleAge   [2] = 2;
            ruleAge   [3] = 1;
            ruleAge   [4] = 0;
            ruleAge   [5] = 1;
            ruleAge   [6] = 0;
            ruleCell  [0] = 1;  ruleState [0] = 6;  ruleNum   [0] = 2;  ruleResult[0] = 4;
            ruleCell  [1] = 5;  ruleState [1] = 1;  ruleNum   [1] = 1;  ruleResult[1] = 4;
            ruleCell  [2] = 1;  ruleState [2] = 6;  ruleNum   [2] = 3;  ruleResult[2] = 6;
            ruleCell  [3] = 0;  ruleState [3] = 3;  ruleNum   [3] = 1;  ruleResult[3] = 5;
            ruleCell  [4] = 2;  ruleState [4] = 3;  ruleNum   [4] = 3;  ruleResult[4] = 6;
            ruleCell  [5] = 1;  ruleState [5] = 6;  ruleNum   [5] = 3;  ruleResult[5] = 0;
            ruleCell  [6] = 3;  ruleState [6] = 5;  ruleNum   [6] = 1;  ruleResult[6] = 1;
            ruleCell  [7] = 6;  ruleState [7] = 2;  ruleNum   [7] = 1;  ruleResult[7] = 4;
            ruleCell  [8] = 2;  ruleState [8] = 1;  ruleNum   [8] = 2;  ruleResult[8] = 6;
            ruleCell  [9] = 4;  ruleState [9] = 4;  ruleNum   [9] = 3;  ruleResult[9] = 2;
            ruleCell  [10] = 2;  ruleState [10] = 1;  ruleNum   [10] = 1;  ruleResult[10] = 0;
            ruleCell  [11] = 5;  ruleState [11] = 4;  ruleNum   [11] = 3;  ruleResult[11] = 6;
            ruleCell  [12] = 3;  ruleState [12] = 1;  ruleNum   [12] = 3;  ruleResult[12] = 4;
            ruleCell  [13] = 5;  ruleState [13] = 4;  ruleNum   [13] = 1;  ruleResult[13] = 3;
            ruleCell  [14] = 3;  ruleState [14] = 6;  ruleNum   [14] = 3;  ruleResult[14] = 1;
            ruleCell  [15] = 6;  ruleState [15] = 3;  ruleNum   [15] = 3;  ruleResult[15] = 5;
            ruleCell  [16] = 5;  ruleState [16] = 3;  ruleNum   [16] = 2;  ruleResult[16] = 0;
            ruleCell  [17] = 3;  ruleState [17] = 3;  ruleNum   [17] = 3;  ruleResult[17] = 6;
            ruleCell  [18] = 2;  ruleState [18] = 3;  ruleNum   [18] = 3;  ruleResult[18] = 1;
            ruleCell  [19] = 4;  ruleState [19] = 4;  ruleNum   [19] = 2;  ruleResult[19] = 6;
            ruleCell  [20] = 1;  ruleState [20] = 2;  ruleNum   [20] = 3;  ruleResult[20] = 3;
            ruleCell  [21] = 0;  ruleState [21] = 2;  ruleNum   [21] = 3;  ruleResult[21] = 0;
            ruleCell  [22] = 3;  ruleState [22] = 6;  ruleNum   [22] = 1;  ruleResult[22] = 1;
            ruleCell  [23] = 1;  ruleState [23] = 2;  ruleNum   [23] = 2;  ruleResult[23] = 3;
            ruleCell  [24] = 1;  ruleState [24] = 4;  ruleNum   [24] = 1;  ruleResult[24] = 5;
            ruleCell  [25] = 6;  ruleState [25] = 4;  ruleNum   [25] = 1;  ruleResult[25] = 4;
            ruleCell  [26] = 3;  ruleState [26] = 4;  ruleNum   [26] = 3;  ruleResult[26] = 2;
            ruleCell  [27] = 2;  ruleState [27] = 4;  ruleNum   [27] = 1;  ruleResult[27] = 1;
            ruleCell  [28] = 5;  ruleState [28] = 5;  ruleNum   [28] = 2;  ruleResult[28] = 5;
            ruleCell  [29] = 6;  ruleState [29] = 2;  ruleNum   [29] = 3;  ruleResult[29] = 4;
            ruleCell  [30] = 2;  ruleState [30] = 2;  ruleNum   [30] = 2;  ruleResult[30] = 1;
            ruleCell  [31] = 5;  ruleState [31] = 4;  ruleNum   [31] = 1;  ruleResult[31] = 3;
            ruleCell  [32] = 6;  ruleState [32] = 2;  ruleNum   [32] = 1;  ruleResult[32] = 2;
            ruleCell  [33] = 1;  ruleState [33] = 1;  ruleNum   [33] = 1;  ruleResult[33] = 1;
            ruleCell  [34] = 1;  ruleState [34] = 5;  ruleNum   [34] = 2;  ruleResult[34] = 0;
            ruleCell  [35] = 5;  ruleState [35] = 1;  ruleNum   [35] = 3;  ruleResult[35] = 1;
            ruleCell  [36] = 1;  ruleState [36] = 2;  ruleNum   [36] = 3;  ruleResult[36] = 0;
            ruleCell  [37] = 1;  ruleState [37] = 4;  ruleNum   [37] = 2;  ruleResult[37] = 4;
            ruleCell  [38] = 0;  ruleState [38] = 4;  ruleNum   [38] = 1;  ruleResult[38] = 0;
            ruleCell  [39] = 0;  ruleState [39] = 4;  ruleNum   [39] = 3;  ruleResult[39] = 4;
		}
		else if (p == 4 )
		{
		    //wiggle
            ruleAge   [0] = 0;
            ruleAge   [1] = 2;
            ruleAge   [2] = 2;
            ruleAge   [3] = 0;
            ruleAge   [4] = 2;
            ruleAge   [5] = 1;
            ruleAge   [6] = 1;
            ruleCell  [0] = 2;  ruleState [0] = 3;  ruleNum   [0] = 1;  ruleResult[0] = 3;
            ruleCell  [1] = 6;  ruleState [1] = 2;  ruleNum   [1] = 3;  ruleResult[1] = 2;
            ruleCell  [2] = 0;  ruleState [2] = 2;  ruleNum   [2] = 3;  ruleResult[2] = 0;
            ruleCell  [3] = 1;  ruleState [3] = 2;  ruleNum   [3] = 2;  ruleResult[3] = 2;
            ruleCell  [4] = 3;  ruleState [4] = 1;  ruleNum   [4] = 1;  ruleResult[4] = 4;
            ruleCell  [5] = 1;  ruleState [5] = 6;  ruleNum   [5] = 2;  ruleResult[5] = 0;
            ruleCell  [6] = 2;  ruleState [6] = 3;  ruleNum   [6] = 3;  ruleResult[6] = 1;
            ruleCell  [7] = 0;  ruleState [7] = 1;  ruleNum   [7] = 2;  ruleResult[7] = 5;
            ruleCell  [8] = 6;  ruleState [8] = 3;  ruleNum   [8] = 3;  ruleResult[8] = 6;
            ruleCell  [9] = 3;  ruleState [9] = 3;  ruleNum   [9] = 1;  ruleResult[9] = 4;
            ruleCell  [10] = 3;  ruleState [10] = 2;  ruleNum   [10] = 3;  ruleResult[10] = 4;
            ruleCell  [11] = 5;  ruleState [11] = 6;  ruleNum   [11] = 3;  ruleResult[11] = 3;
            ruleCell  [12] = 4;  ruleState [12] = 6;  ruleNum   [12] = 3;  ruleResult[12] = 3;
            ruleCell  [13] = 0;  ruleState [13] = 6;  ruleNum   [13] = 1;  ruleResult[13] = 0;
            ruleCell  [14] = 4;  ruleState [14] = 3;  ruleNum   [14] = 1;  ruleResult[14] = 2;
            ruleCell  [15] = 1;  ruleState [15] = 6;  ruleNum   [15] = 1;  ruleResult[15] = 0;
            ruleCell  [16] = 6;  ruleState [16] = 4;  ruleNum   [16] = 3;  ruleResult[16] = 2;
            ruleCell  [17] = 2;  ruleState [17] = 1;  ruleNum   [17] = 1;  ruleResult[17] = 1;
            ruleCell  [18] = 3;  ruleState [18] = 1;  ruleNum   [18] = 2;  ruleResult[18] = 3;
            ruleCell  [19] = 6;  ruleState [19] = 4;  ruleNum   [19] = 2;  ruleResult[19] = 4;
            ruleCell  [20] = 0;  ruleState [20] = 4;  ruleNum   [20] = 2;  ruleResult[20] = 2;
            ruleCell  [21] = 5;  ruleState [21] = 3;  ruleNum   [21] = 2;  ruleResult[21] = 0;
            ruleCell  [22] = 5;  ruleState [22] = 1;  ruleNum   [22] = 2;  ruleResult[22] = 4;
            ruleCell  [23] = 0;  ruleState [23] = 2;  ruleNum   [23] = 3;  ruleResult[23] = 3;
            ruleCell  [24] = 5;  ruleState [24] = 6;  ruleNum   [24] = 3;  ruleResult[24] = 4;
            ruleCell  [25] = 3;  ruleState [25] = 2;  ruleNum   [25] = 1;  ruleResult[25] = 0;
            ruleCell  [26] = 4;  ruleState [26] = 3;  ruleNum   [26] = 2;  ruleResult[26] = 2;
            ruleCell  [27] = 4;  ruleState [27] = 4;  ruleNum   [27] = 2;  ruleResult[27] = 3;
            ruleCell  [28] = 2;  ruleState [28] = 2;  ruleNum   [28] = 2;  ruleResult[28] = 5;
            ruleCell  [29] = 2;  ruleState [29] = 5;  ruleNum   [29] = 2;  ruleResult[29] = 6;
            ruleCell  [30] = 0;  ruleState [30] = 2;  ruleNum   [30] = 2;  ruleResult[30] = 2;
            ruleCell  [31] = 3;  ruleState [31] = 1;  ruleNum   [31] = 2;  ruleResult[31] = 4;
            ruleCell  [32] = 4;  ruleState [32] = 6;  ruleNum   [32] = 2;  ruleResult[32] = 1;
            ruleCell  [33] = 4;  ruleState [33] = 1;  ruleNum   [33] = 1;  ruleResult[33] = 4;
            ruleCell  [34] = 3;  ruleState [34] = 6;  ruleNum   [34] = 1;  ruleResult[34] = 1;
            ruleCell  [35] = 1;  ruleState [35] = 1;  ruleNum   [35] = 2;  ruleResult[35] = 2;
            ruleCell  [36] = 1;  ruleState [36] = 5;  ruleNum   [36] = 1;  ruleResult[36] = 5;
            ruleCell  [37] = 0;  ruleState [37] = 2;  ruleNum   [37] = 2;  ruleResult[37] = 2;
            ruleCell  [38] = 6;  ruleState [38] = 1;  ruleNum   [38] = 3;  ruleResult[38] = 1;
            ruleCell  [39] = 0;  ruleState [39] = 3;  ruleNum   [39] = 3;  ruleResult[39] = 1;
		}
		else if (p == 5 )
		{
		    //islands
            ruleAge   [0] = 2;
            ruleAge   [1] = 2;
            ruleAge   [2] = 1;
            ruleAge   [3] = 2;
            ruleAge   [4] = 2;
            ruleAge   [5] = 1;
            ruleAge   [6] = 1;
            ruleCell  [0] = 5;  ruleState [0] = 1;  ruleNum   [0] = 1;  ruleResult[0] = 3;
            ruleCell  [1] = 3;  ruleState [1] = 3;  ruleNum   [1] = 1;  ruleResult[1] = 3;
            ruleCell  [2] = 2;  ruleState [2] = 2;  ruleNum   [2] = 3;  ruleResult[2] = 2;
            ruleCell  [3] = 4;  ruleState [3] = 3;  ruleNum   [3] = 3;  ruleResult[3] = 5;
            ruleCell  [4] = 6;  ruleState [4] = 2;  ruleNum   [4] = 2;  ruleResult[4] = 0;
            ruleCell  [5] = 4;  ruleState [5] = 1;  ruleNum   [5] = 1;  ruleResult[5] = 4;
            ruleCell  [6] = 0;  ruleState [6] = 5;  ruleNum   [6] = 1;  ruleResult[6] = 2;
            ruleCell  [7] = 6;  ruleState [7] = 3;  ruleNum   [7] = 2;  ruleResult[7] = 6;
            ruleCell  [8] = 0;  ruleState [8] = 1;  ruleNum   [8] = 2;  ruleResult[8] = 6;
            ruleCell  [9] = 0;  ruleState [9] = 6;  ruleNum   [9] = 3;  ruleResult[9] = 1;
            ruleCell  [10] = 5;  ruleState [10] = 1;  ruleNum   [10] = 3;  ruleResult[10] = 1;
            ruleCell  [11] = 3;  ruleState [11] = 6;  ruleNum   [11] = 3;  ruleResult[11] = 0;
            ruleCell  [12] = 5;  ruleState [12] = 5;  ruleNum   [12] = 1;  ruleResult[12] = 1;
            ruleCell  [13] = 0;  ruleState [13] = 4;  ruleNum   [13] = 1;  ruleResult[13] = 5;
            ruleCell  [14] = 3;  ruleState [14] = 1;  ruleNum   [14] = 2;  ruleResult[14] = 6;
            ruleCell  [15] = 2;  ruleState [15] = 6;  ruleNum   [15] = 2;  ruleResult[15] = 2;
            ruleCell  [16] = 3;  ruleState [16] = 2;  ruleNum   [16] = 3;  ruleResult[16] = 1;
            ruleCell  [17] = 5;  ruleState [17] = 1;  ruleNum   [17] = 2;  ruleResult[17] = 5;
            ruleCell  [18] = 4;  ruleState [18] = 6;  ruleNum   [18] = 1;  ruleResult[18] = 2;
            ruleCell  [19] = 3;  ruleState [19] = 5;  ruleNum   [19] = 2;  ruleResult[19] = 4;
            ruleCell  [20] = 6;  ruleState [20] = 2;  ruleNum   [20] = 2;  ruleResult[20] = 1;
            ruleCell  [21] = 0;  ruleState [21] = 3;  ruleNum   [21] = 3;  ruleResult[21] = 2;
            ruleCell  [22] = 5;  ruleState [22] = 1;  ruleNum   [22] = 3;  ruleResult[22] = 0;
            ruleCell  [23] = 4;  ruleState [23] = 6;  ruleNum   [23] = 3;  ruleResult[23] = 2;
            ruleCell  [24] = 1;  ruleState [24] = 4;  ruleNum   [24] = 1;  ruleResult[24] = 2;
            ruleCell  [25] = 5;  ruleState [25] = 3;  ruleNum   [25] = 3;  ruleResult[25] = 2;
            ruleCell  [26] = 2;  ruleState [26] = 1;  ruleNum   [26] = 2;  ruleResult[26] = 5;
            ruleCell  [27] = 1;  ruleState [27] = 2;  ruleNum   [27] = 2;  ruleResult[27] = 0;
            ruleCell  [28] = 0;  ruleState [28] = 4;  ruleNum   [28] = 1;  ruleResult[28] = 5;
            ruleCell  [29] = 1;  ruleState [29] = 6;  ruleNum   [29] = 1;  ruleResult[29] = 5;
            ruleCell  [30] = 5;  ruleState [30] = 3;  ruleNum   [30] = 2;  ruleResult[30] = 3;
            ruleCell  [31] = 2;  ruleState [31] = 5;  ruleNum   [31] = 2;  ruleResult[31] = 1;
            ruleCell  [32] = 3;  ruleState [32] = 1;  ruleNum   [32] = 2;  ruleResult[32] = 2;
            ruleCell  [33] = 3;  ruleState [33] = 4;  ruleNum   [33] = 3;  ruleResult[33] = 6;
            ruleCell  [34] = 1;  ruleState [34] = 2;  ruleNum   [34] = 1;  ruleResult[34] = 3;
            ruleCell  [35] = 4;  ruleState [35] = 2;  ruleNum   [35] = 3;  ruleResult[35] = 4;
            ruleCell  [36] = 4;  ruleState [36] = 4;  ruleNum   [36] = 2;  ruleResult[36] = 4;
            ruleCell  [37] = 1;  ruleState [37] = 1;  ruleNum   [37] = 2;  ruleResult[37] = 0;
            ruleCell  [38] = 6;  ruleState [38] = 5;  ruleNum   [38] = 3;  ruleResult[38] = 3;
            ruleCell  [39] = 3;  ruleState [39] = 4;  ruleNum   [39] = 3;  ruleResult[39] = 0;		

		}
		else if (p == 6 )
		{
            //replicate
            ruleAge   [0] = 0;
            ruleAge   [1] = 0;
            ruleAge   [2] = 2;
            ruleAge   [3] = 1;
            ruleAge   [4] = 2;
            ruleAge   [5] = 2;
            ruleAge   [6] = 0;
            ruleCell  [0] = 4;  ruleState [0] = 1;  ruleNum   [0] = 1;  ruleResult[0] = 5;
            ruleCell  [1] = 0;  ruleState [1] = 3;  ruleNum   [1] = 2;  ruleResult[1] = 0;
            ruleCell  [2] = 5;  ruleState [2] = 6;  ruleNum   [2] = 2;  ruleResult[2] = 6;
            ruleCell  [3] = 2;  ruleState [3] = 3;  ruleNum   [3] = 2;  ruleResult[3] = 4;
            ruleCell  [4] = 4;  ruleState [4] = 1;  ruleNum   [4] = 3;  ruleResult[4] = 5;
            ruleCell  [5] = 2;  ruleState [5] = 5;  ruleNum   [5] = 2;  ruleResult[5] = 0;
            ruleCell  [6] = 1;  ruleState [6] = 6;  ruleNum   [6] = 2;  ruleResult[6] = 0;
            ruleCell  [7] = 1;  ruleState [7] = 6;  ruleNum   [7] = 3;  ruleResult[7] = 5;
            ruleCell  [8] = 6;  ruleState [8] = 3;  ruleNum   [8] = 1;  ruleResult[8] = 1;
            ruleCell  [9] = 3;  ruleState [9] = 4;  ruleNum   [9] = 2;  ruleResult[9] = 4;
            ruleCell  [10] = 0;  ruleState [10] = 6;  ruleNum   [10] = 3;  ruleResult[10] = 4;
            ruleCell  [11] = 5;  ruleState [11] = 5;  ruleNum   [11] = 3;  ruleResult[11] = 4;
            ruleCell  [12] = 0;  ruleState [12] = 4;  ruleNum   [12] = 3;  ruleResult[12] = 2;
            ruleCell  [13] = 6;  ruleState [13] = 5;  ruleNum   [13] = 3;  ruleResult[13] = 6;
            ruleCell  [14] = 5;  ruleState [14] = 1;  ruleNum   [14] = 3;  ruleResult[14] = 1;
            ruleCell  [15] = 1;  ruleState [15] = 1;  ruleNum   [15] = 1;  ruleResult[15] = 4;
            ruleCell  [16] = 1;  ruleState [16] = 1;  ruleNum   [16] = 2;  ruleResult[16] = 3;
            ruleCell  [17] = 2;  ruleState [17] = 4;  ruleNum   [17] = 2;  ruleResult[17] = 0;
            ruleCell  [18] = 4;  ruleState [18] = 4;  ruleNum   [18] = 3;  ruleResult[18] = 1;
            ruleCell  [19] = 0;  ruleState [19] = 4;  ruleNum   [19] = 1;  ruleResult[19] = 5;
            ruleCell  [20] = 6;  ruleState [20] = 3;  ruleNum   [20] = 3;  ruleResult[20] = 0;
            ruleCell  [21] = 1;  ruleState [21] = 2;  ruleNum   [21] = 2;  ruleResult[21] = 2;
            ruleCell  [22] = 5;  ruleState [22] = 5;  ruleNum   [22] = 3;  ruleResult[22] = 1;
            ruleCell  [23] = 3;  ruleState [23] = 3;  ruleNum   [23] = 3;  ruleResult[23] = 2;
            ruleCell  [24] = 2;  ruleState [24] = 5;  ruleNum   [24] = 1;  ruleResult[24] = 5;
            ruleCell  [25] = 6;  ruleState [25] = 6;  ruleNum   [25] = 3;  ruleResult[25] = 0;
            ruleCell  [26] = 6;  ruleState [26] = 6;  ruleNum   [26] = 2;  ruleResult[26] = 0;
            ruleCell  [27] = 1;  ruleState [27] = 3;  ruleNum   [27] = 1;  ruleResult[27] = 2;
            ruleCell  [28] = 6;  ruleState [28] = 5;  ruleNum   [28] = 2;  ruleResult[28] = 1;
            ruleCell  [29] = 4;  ruleState [29] = 6;  ruleNum   [29] = 3;  ruleResult[29] = 2;
            ruleCell  [30] = 5;  ruleState [30] = 2;  ruleNum   [30] = 3;  ruleResult[30] = 3;
            ruleCell  [31] = 3;  ruleState [31] = 3;  ruleNum   [31] = 2;  ruleResult[31] = 1;
            ruleCell  [32] = 6;  ruleState [32] = 4;  ruleNum   [32] = 1;  ruleResult[32] = 3;
            ruleCell  [33] = 0;  ruleState [33] = 1;  ruleNum   [33] = 2;  ruleResult[33] = 0;
            ruleCell  [34] = 3;  ruleState [34] = 6;  ruleNum   [34] = 1;  ruleResult[34] = 5;
            ruleCell  [35] = 3;  ruleState [35] = 5;  ruleNum   [35] = 3;  ruleResult[35] = 2;
            ruleCell  [36] = 2;  ruleState [36] = 1;  ruleNum   [36] = 1;  ruleResult[36] = 2;
            ruleCell  [37] = 5;  ruleState [37] = 6;  ruleNum   [37] = 2;  ruleResult[37] = 2;
            ruleCell  [38] = 5;  ruleState [38] = 5;  ruleNum   [38] = 1;  ruleResult[38] = 3;
            ruleCell  [39] = 6;  ruleState [39] = 4;  ruleNum   [39] = 1;  ruleResult[39] = 2;
		}
		else if (p == 7 )
		{	
			// storms
            ruleAge   [0] = 1;
            ruleAge   [1] = 0;
            ruleAge   [2] = 0;
            ruleAge   [3] = 0;
            ruleAge   [4] = 2;
            ruleAge   [5] = 1;
            ruleAge   [6] = 2;
            ruleCell  [0] = 6;  ruleState [0] = 2;  ruleNum   [0] = 1;  ruleResult[0] = 2;
            ruleCell  [1] = 5;  ruleState [1] = 2;  ruleNum   [1] = 3;  ruleResult[1] = 1;
            ruleCell  [2] = 5;  ruleState [2] = 6;  ruleNum   [2] = 3;  ruleResult[2] = 6;
            ruleCell  [3] = 3;  ruleState [3] = 1;  ruleNum   [3] = 2;  ruleResult[3] = 3;
            ruleCell  [4] = 3;  ruleState [4] = 1;  ruleNum   [4] = 1;  ruleResult[4] = 3;
            ruleCell  [5] = 2;  ruleState [5] = 1;  ruleNum   [5] = 1;  ruleResult[5] = 5;
            ruleCell  [6] = 0;  ruleState [6] = 5;  ruleNum   [6] = 1;  ruleResult[6] = 4;
            ruleCell  [7] = 3;  ruleState [7] = 5;  ruleNum   [7] = 3;  ruleResult[7] = 0;
            ruleCell  [8] = 0;  ruleState [8] = 5;  ruleNum   [8] = 1;  ruleResult[8] = 5;
            ruleCell  [9] = 3;  ruleState [9] = 1;  ruleNum   [9] = 3;  ruleResult[9] = 1;
            ruleCell  [10] = 6;  ruleState [10] = 5;  ruleNum   [10] = 1;  ruleResult[10] = 2;
            ruleCell  [11] = 0;  ruleState [11] = 5;  ruleNum   [11] = 1;  ruleResult[11] = 3;
            ruleCell  [12] = 6;  ruleState [12] = 4;  ruleNum   [12] = 3;  ruleResult[12] = 3;
            ruleCell  [13] = 3;  ruleState [13] = 2;  ruleNum   [13] = 2;  ruleResult[13] = 2;
            ruleCell  [14] = 5;  ruleState [14] = 3;  ruleNum   [14] = 2;  ruleResult[14] = 1;
            ruleCell  [15] = 2;  ruleState [15] = 3;  ruleNum   [15] = 1;  ruleResult[15] = 3;
            ruleCell  [16] = 1;  ruleState [16] = 3;  ruleNum   [16] = 1;  ruleResult[16] = 5;
            ruleCell  [17] = 1;  ruleState [17] = 6;  ruleNum   [17] = 2;  ruleResult[17] = 1;
            ruleCell  [18] = 0;  ruleState [18] = 3;  ruleNum   [18] = 2;  ruleResult[18] = 6;
            ruleCell  [19] = 2;  ruleState [19] = 3;  ruleNum   [19] = 1;  ruleResult[19] = 2;
            ruleCell  [20] = 6;  ruleState [20] = 5;  ruleNum   [20] = 2;  ruleResult[20] = 5;
            ruleCell  [21] = 2;  ruleState [21] = 4;  ruleNum   [21] = 3;  ruleResult[21] = 3;
            ruleCell  [22] = 2;  ruleState [22] = 1;  ruleNum   [22] = 3;  ruleResult[22] = 0;
            ruleCell  [23] = 0;  ruleState [23] = 4;  ruleNum   [23] = 3;  ruleResult[23] = 0;
            ruleCell  [24] = 5;  ruleState [24] = 3;  ruleNum   [24] = 3;  ruleResult[24] = 0;
            ruleCell  [25] = 0;  ruleState [25] = 1;  ruleNum   [25] = 3;  ruleResult[25] = 0;
            ruleCell  [26] = 4;  ruleState [26] = 6;  ruleNum   [26] = 2;  ruleResult[26] = 4;
            ruleCell  [27] = 1;  ruleState [27] = 4;  ruleNum   [27] = 3;  ruleResult[27] = 3;
            ruleCell  [28] = 5;  ruleState [28] = 4;  ruleNum   [28] = 3;  ruleResult[28] = 1;
            ruleCell  [29] = 6;  ruleState [29] = 6;  ruleNum   [29] = 3;  ruleResult[29] = 3;
            ruleCell  [30] = 2;  ruleState [30] = 6;  ruleNum   [30] = 2;  ruleResult[30] = 3;
            ruleCell  [31] = 1;  ruleState [31] = 5;  ruleNum   [31] = 2;  ruleResult[31] = 3;
            ruleCell  [32] = 3;  ruleState [32] = 3;  ruleNum   [32] = 1;  ruleResult[32] = 2;
            ruleCell  [33] = 4;  ruleState [33] = 1;  ruleNum   [33] = 3;  ruleResult[33] = 0;
            ruleCell  [34] = 2;  ruleState [34] = 3;  ruleNum   [34] = 2;  ruleResult[34] = 3;
            ruleCell  [35] = 3;  ruleState [35] = 5;  ruleNum   [35] = 1;  ruleResult[35] = 1;
            ruleCell  [36] = 1;  ruleState [36] = 3;  ruleNum   [36] = 3;  ruleResult[36] = 2;
            ruleCell  [37] = 0;  ruleState [37] = 1;  ruleNum   [37] = 1;  ruleResult[37] = 3;
            ruleCell  [38] = 1;  ruleState [38] = 5;  ruleNum   [38] = 1;  ruleResult[38] = 3;
            ruleCell  [39] = 6;  ruleState [39] = 1;  ruleNum   [39] = 1;  ruleResult[39] = 3;

		}
		
		for (var i = 0; i < NUM_INDIVIDUALS; i++) 
		{
			fitness[i] = Math.random() * AVERAGE_RANDOM_FITNESS;
		}
    }
		
		
	
	
	
	//------------------------------------------------------------
	// start that puppy up!
	//------------------------------------------------------------

    //-------------------------------------
    // initialize as icosa-geodesic
    //-------------------------------------
    this.numCells = NUM_ICOSA_POINTS;
    
    for (var c=0; c<this.numCells; c++)
    {
        this.cell[c].initialized = true;
    }

    this.putIcosaPointsOnSphere();

	//this.createRulesFromGenes( currentIndividual );
	this.loadPresetRules( 2 ); 

	
	//------------------------------------------
	// set up the buttons
	//------------------------------------------
	this.arrangeButtons();
	
	
		
	//------------------------------------------------------------
	// render the buttons
	//------------------------------------------------------------
//for (var b=0; b<NUM_BUTTONS; b++)
for (var b=0; b<8; b++)
	{
		this.renderButton(b, false);
	}

	//-------------------------------------------
	// render population....
	//-------------------------------------------
	//this.renderPopulation();		
	
	//------------------------------------------------------------
	// start up the timer
	//------------------------------------------------------------
	this.timer = setTimeout( "cells.update()", MILLISECONDS_PER_UPDATE );		



	//-------------------------------------------------------------------------------------------
	this.resize = function( width, height )
	{
		canvas.clearRect( 0, 0, document.body.clientWidth, document.body.clientHeight );

	    this.Xcenter = document.body.clientWidth / 2;
	    this.arrangeButtons();
            
        //------------------------------------------------------------
        // render the buttons
        //------------------------------------------------------------
        for (var b=0; b<8; b++)
        {
            this.renderButton(b, false);
        }	    
	}
	
} //--------------------------------------------------------------------
 //---------------       end of Cells()       -------------------------
//--------------------------------------------------------------------

//---------------------------------------
document.onmousedown = function(e) 
{
    cells.mouseDown( e.pageX, e.pageY );
}

//---------------------------------------
document.onmousemove = function(e) 
{
    cells.mouseMove( e.pageX, e.pageY );
}

//---------------------------------------
document.onmouseup = function(e) 
{
    cells.mouseUp( e.pageX, e.pageY );
}



(define-type grid-node x y walkable? g h previous)
(define (grid-node-reset gn)
  (grid-node-walkable?-set! gn #t)
  (grid-node-g-set! gn +inf.0)
  (grid-node-h-set! gn +inf.0)
  (grid-node-previous-set! #f)
  grid-node)
(define (grid-node-f grid-node)
  (+ (grid-node-g grid-node)
	 (grid-node-g grid-node)))

(define-type grid w h data)
(define (grid-index grid x y)
  (let ((w (grid-w grid)))
	(+ x (* y w))))

(define (grid-ref grid x y)
  (vector-ref (grid-data grid) (grid-index grid x y)))

(define (grid-ref-or grid x y orval)
  (if (grid-on? grid x y)
	  (grid-ref grid x y)
	  orval))

(define (grid-on? grid x y)
  (and (>= x 0)
	   (>= y 0)
	   (< x (grid-w grid))
	   (< y (grid-h grid))))

(define (grid-ref-walkable-only-or grid x y)
  (if (or (not (grid-on? grid x y))
		  (and (grid-on? grid x y) 
			   (not (grid-walkable-at? grid x y))))
	  #f
	  (grid-ref grid x y)))

(define (grid-walkable-at? grid x y)
  (grid-node-walkable? (grid-ref grid x y)))

(define (grid-set-one! grid i j v)
  (vector-set! (grid-data grid) 
			   (grid-index grid i j) 
			   v))

(define (grid-for-each-pair fun lst)
  (let* ((count (length lst)))
	(if (not (= 0 (modulo count 2)))
		(error "for-each-pair requires a list whose length is divisible by two.")
		(let loop ((pairs lst)
				   (remaining count))
		  (if (= 0 remaining) #t
			  (begin 
				(fun (car pairs)
					 (cadr pairs))
				(loop (cddr pairs)
					  (- remaining 2))))))))

(define (grid-for-each-triple fun lst)
  (let* ((count (length lst)))
	(if (not (= 0 (modulo count 3)))
		(error "for-each-triple requires a list whose length is divisible by three.")
		(let loop ((triples lst)
				   (remaining count))
		  (if (= 0 remaining) #t
			  (begin 
				(fun (car triples)
					 (cadr triples)
					 (caddr triples))
				(loop (cdddr triples)
					  (- remaining 3))))))))

(define (grid-set! grid #!rest triples)
  (grid-for-each-triple (lambda (i j v)
					 (grid-set-one! grid i j v))
				   triples))

(define (grid-forbid-single! grid i j)
  (grid-node-walkable?-set! (grid-ref grid i j) #f))

(define (grid-forbid! grid #!rest pairs)
  (grid-for-each-pair (lambda (i j)
						(grid-forbid-single! grid i j))
					  pairs))

(define (grid-allow-single! grid i j)
  (grid-node-walkable?-set! (grid-ref grid i j) #t))

(define (grid-allow! grid #!rest pairs)
  (grid-for-each-pair (lambda (i j)
						(grid-allow-single! grid i j))
					  pairs))


(define (make-grid* w h #!optional (init (lambda (i j)
										   (make-grid-node 
											i j #t
											+inf.0 +inf.0
											#f))))
  (let* ((vec (make-vector (* w h)))
		 (grid (make-grid w h vec)))
	(let loop-x 
		((x 0))
	  (if (>= x w)
		  grid
		  (begin
			(let loop-y ((y 0))
			  (if (>= y h)
				  grid
				  (begin 
					(grid-set! grid x y (init x y))
					(loop-y (+ y 1)))))
			(loop-x (+ x 1)))))))

(define (grid-for-each-node f grid)
  (let ((w (grid-w grid))
		(h (grid-w grid)))
	(let loop-y
		((y 0))
	  (if (< y h)
		  (begin 
			(let loop-x
				((x 0))
			  (if (< x w)
				  (begin 
					(f (grid-ref grid x y))
					(loop-x (+ x 1)))
				  grid))
			(loop-y (+ y 1)))
		  grid))))

(define (display-grid grid)
  (let ((w (grid-w grid))
		(h (grid-w grid))) 
	(let yloop ((y 0))
	  (if (< y h) 
		  (begin 
			(let xloop ((x 0))
			 (if (< x w)
				 (begin (display 
						 (if (grid-walkable-at? grid x y) "O" "X"))
						(xloop (+ x 1)))
				 (newline)))
			(yloop (+ y 1)))
		  grid))))

(define (node< n1 n2)
  (< (grid-node-f n1)
	 (grid-node-f n2)))

(define (manhattan-distance x0 y0 xf yf)
  (+ (abs (- x0 xf))
	 (abs (- y0 yf))))

(define (a*-coords-eq? x1 y1 x2 y2)
  (and (= x1 x2)
	   (= y1 y2)))

(define (grid-walkable-neighbors grid node)
  (let ((x (grid-node-x node))
		(y (grid-node-y node)))
	(let loop ((pairs '(-1 0 1 0 0 -1 0 1))
			   (nodes '()))
	  (if (eq? '() pairs)
		  nodes
		  (let ((node (grid-ref-walkable-only-or 
					   grid
					   (+ x (car pairs))
					   (+ y (cadr pairs)))))
			(if node 
				(loop (cddr pairs)
					  (cons node nodes))
				(loop (cddr pairs)
					  nodes)))))))

(define (a*! xs ys xf yf grid)
  (define open-set (make-heap* node<))
  (if (not (grid-walkable-at? grid xs ys))
	  (error (list "Grid is marked as unwalkable at start position: " xs ys)))
  (if (not (grid-walkable-at? grid xf yf))
	  (error (list "Grid is marked as unwalkable at end position: " xf yf)))
  (heap-add! open-set (grid-ref grid xs ys))
  (let ((start-node (grid-ref grid xs ys)))
	(grid-node-g-set! start-node 0))
  (let while ((current (heap-pop! open-set)))
	(cond 
	 ((heap-null-value? current)
	  #f)
	 ((a*-coords-eq? xf yf (grid-node-x current) (grid-node-y current))
	  (grid-node-reconstruct-path current))
	 (#t 
	  (let loop ((neighbors (grid-walkable-neighbors grid current)))
		(if (eq? neighbors '())
			#t
			(let* 
				((neighbor (car neighbors))
				 (tentative-g (+ 
							   (grid-node-g current)
							   (manhattan-distance (grid-node-x current)
												   (grid-node-y current)
												   (grid-node-x neighbor)
												   (grid-node-y neighbor))))
				 (neighbors (cdr neighbors)))			  
			  (if (< tentative-g (grid-node-g neighbor))
				  (begin 
					(heap-add! open-set neighbor)
					(grid-node-previous-set! neighbor current)
					(grid-node-g-set! neighbor tentative-g)
					(grid-node-h-set! neighbor (manhattan-distance 
												(grid-node-x neighbor)
												(grid-node-y neighbor)
												xf yf)))
				  #t)
			  (loop neighbors))))
	  (while (heap-pop! open-set))))))

(define (grid-node-reconstruct-path node)
  (let loop ((path (list (list (grid-node-x node)
							   (grid-node-y node))))
			 (node node))
	(let ((previous (grid-node-previous node)))
	  (cond 
	   (previous (loop (cons (list (grid-node-x previous)
								   (grid-node-y previous)) path)
					   previous))
	   (#t path)))))

(define (grid-reset-scores! grid)
  (grid-for-each-node 
   (lambda (node)
	 (grid-node-g-set! node +inf.0)
	 (grid-node-h-set! node +inf.0)
	 (grid-node-previous-set! node #f))
   grid))

(define (grid-reset! grid)
  (grid-for-each-node 
   (lambda (node)
	 (grid-node-g-set! node +inf.0)
	 (grid-node-h-set! node +inf.0)
	 (grid-node-walkable?-set! node #t)
	 (grid-node-previous-set! node #f))
   grid))

(define (display-grid-and-path grid path)
  (define (point-in-path? x y path)
	(cond ((eq? path '())
		   #f)
		  ((and (= (car (car path)) x)
				(= (cadr (car path)) y))
		   #t)
		  (#t 
		   (point-in-path? x y (cdr path)))))
  (if path
	  (let ((w (grid-w grid))
			(h (grid-w grid))) 
		(let yloop ((y 0))
		  (if (< y h) 
			  (begin 
				(let xloop ((x 0))
				  (if (< x w)
					  (begin (display 
							  (cond 
							   ((not (grid-walkable-at? grid x y)) "X")
							   ((point-in-path? x y path)
								"+")
							   (#t ".")))
							 (xloop (+ x 1)))
					  (newline)))
				(yloop (+ y 1)))
			  grid)))
	  (display-grid grid)))

(define (grid-north x y)
  (list x (- y 1)))

(define (grid-south x y)
  (list x (+ y 1)))

(define (grid-east x y)
  (list (+ x 1) y))

(define (grid-west x y)
  (list (- x 1) y))

(define (grid-forbid-run! grid sx sy dir len)
  (let loop ((node (grid-ref-or grid sx sy #f))
			 (len len))
	(cond 
	 ((and node
		   (> len 0))
	  (let ((x (grid-node-x node))
			(y (grid-node-y node))) 
		(grid-forbid-single! 
			   grid 
			   x
			   y)
	   (loop (let ((new-pos (dir x y)))
			   (grid-ref-or grid (car new-pos) (cadr new-pos) #f))
			 (- len 1))))
	 (#t 'done))))

(define (grid-filter-nodes f grid)
  (let ((output '()))
	(grid-for-each-node 
	 (lambda (node)
	   (if (f node)
		   (set! output (cons node output))
		   #f))
	 grid)
	(reverse output)))

(define (grid-always-true node)
  #t)

;; Note - if a heap is passed in, make sure it is empty.
(define (grid-nodes-ordered-by f grid #!key 
							   (filter grid-always-true) 
							   (heap (make-heap* f size-guess: (vector-length (grid-data grid)))))
  (grid-for-each-node 
   (lambda (node)
	 (if (filter node)
		 (heap-add! node)
		 #t)))
  (heap-empty->list! heap))



 ;; function A*(start,goal) 
 ;;     openset := set containing the initial node // The set of tentative nodes to be evaluated.
 ;;     came_from := the empty map                 // The map of navigated nodes.
 ;;     g_score[start] := 0                        // Distance from start along optimal path.
 ;;     h_score[start] := heuristic_estimate_of_distance(start, goal)
 ;;     f_score[start] := h_score[start]           // Estimated total distance from start to goal through y.
 ;;     while openset is not empty
 ;;         x := the node in openset having the lowest f_score[] value
 ;;         if x = goal
 ;;             return reconstruct_path(came_from, came_from[goal])
 ;;         remove x from openset
 ;;         foreach y in neighbor_nodes(x)
 ;;             tentative_g_score := g_score[x] + dist_between(x,y)
 
 ;;             if g_score[y] is not set or tentative_g_score < g_score[y]
 ;;                 add y to openset
 ;;                 came_from[y] := x
 
 ;;                 g_score[y] := tentative_g_score
 ;;                 h_score[y] := heuristic_estimate_of_distance(y, goal)
 ;;                 f_score[y] := g_score[y] + h_score[y]
 ;;     return failure
 
 ;; function reconstruct_path(came_from, current_node)
 ;;     if came_from[current_node] is set
 ;;         p = reconstruct_path(came_from, came_from[current_node])
 ;;         return (p + current_node)
 ;;     else
 ;;         return current_node

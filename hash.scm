(use-modules (srfi srfi-1)
	     (srfi srfi-9)
	     (srfi srfi-9 gnu))

(define (log2 v)
 (inexact->exact (/ (log v) (log 2))))

(define (bit->bool b)
  (case b
    ((0) #f)
    ((1) #t)
    (else (error "bit->bool: Bit isn't 0 or 1."))))

(define (all-zero? l)
  (not (bit->bool
  	(fold (lambda (a b)
		  (logior a b))
		0
		l))))

(define (all-one? l)
  (bit->bool
    (fold (lambda (a b)
	    (logand a b))
	  1
	  l)))

(define (inc l)
  (reverse
  (cdr
  (fold (lambda (v s)
	  (let ((res (cdr s))
		(carry (car s)))
	    (case v
	      ((0) (cons 0 (cons carry res)))
	      ((1) (case carry
		     ((0) (cons 0 (cons 1 res)))
		     ((1) (cons 1 (cons 0 res))))))))
	(cons 1 '())
	l))))

(define (error-prob error p)
  (let ((p0 (- 1 p))
	(p1 p))
    (fold (lambda (v p)
	    (case v
	      ((0) (* p p0))
	      ((1) (* p p1))))
	  1
	  error)))

(define (apply-error error bits)
  (map (lambda (e b)
	 (logxor e b))
       error
       bits))

(define (invert bits)
  (map (lambda (b)
	 (logxor b 1))
       bits))

(define (product a b)
  (fold logxor 0 (map logand a b)))

(define (exactly-1-1 s)
  (if (not (all-zero? s))
    (= 1 (fold (lambda (in count)
	    (if (= in 1)
	      (1+ count)
	      count))
	  0
	  s))
    #f))

(define (make-simplex-columns n)
  (let loop ((cols '())
	       (cur-col  (inc (make-list n 0))))
    (if (all-one? cur-col)
	;reverse so cols are in numerical order
	;not strictly necessary
	(reverse (cons cur-col cols))
	(loop (cons cur-col cols) (inc cur-col)))))

;;if G=(I|P) then a check matrix H=(P^T|I)
(define (make-hamming-generator n)
  (let* ((p (cols->matrix (filter-identity-cols (make-simplex-columns n))))
	(i (identity-matrix (matrix-columns p))))
    (matrix-concat
      (matrix-transpose p)
      i)))

(define (filter-identity-cols cols)
  (filter (lambda (s)
	    (and (not (exactly-1-1 s))
		 (not (all-zero? s))))
	  cols))

(define (make-simplex-matrix n)
  (matrix-concat
    (identity-matrix n)
    ;remove columns already in identity matrix
    (cols->matrix (filter-identity-cols (make-simplex-columns n)))))

(define (hamming-correct s)
  (let* ((simplex (make-simplex-matrix (log2 (+ (length s) 1))))
	(m (*make-matrix (length s) 1 (list->vector s)))
	(error-col  (vector->list (matrix-data (matrix-product simplex m))))
	(error-index (list-index (lambda (v)
				   (equal? v error-col))
				 (matrix->cols simplex)))
	(error-val (if error-index
		     (list-ref s error-index)
		     #f)))
    
    (if error-val
      (if (= error-val 0)
        (list-set! s error-index 1)
        (list-set! s error-index 0)))
    s))

(define (hamming-decode s)
  (let ((n (log2 (1+ (length s)))))
    (list-tail s n)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Hash table stuff
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;for now we'll set the chunk size to 64 bits.

;We have G=(I|P) and H=(P^t|I)
;G should have 63 columns if it has 6 rows

;---consider adding another row to the identity matrix with zero values
;---across the rest of the matrix to bring the column count up to 64.
;---what would be the properties of the code produced?

;(chunk with 2^n - 1 bits) -> (chunk with 2^n - 1 - n bits)
(define (hash-chunk chunk)
  ;maybe add some length verification for chunk (should be 2^n - 1)
  (hamming-decode (hamming-correct chunk)))

;Optimal asymmetric encryption padding

(define (pad-data data chunk-size)
  (let* ((mod (modulo (length data) chunk-size))
	 (length-diff (if (= mod 0)
			0
			(- chunk-size mod))))
    (append (make-list length-diff 0) data)))

;;Premature optimization thought
;--- streaming hash algorithm. Lazy sort of.
;--- only read in bits as they're needed. Should sort of look like a triangle
;--- with the triangle growing with increasing rounds.

;--- notice (hash-round '(1 1 1 0)) -> '(1 1 1) 
;		and '(0 1 1 1) -> '(1 1 1)

(define (hash-round data chunk-size)
  (let loop ((data (pad-data data chunk-size))
	     (result '()))
    (cond ((eq? '() data) (apply append (reverse result)))
	  ((< (length data) chunk-size)
	   (error "hash-round: data length not a multiple of chunk size."))
	  (else (loop (drop data chunk-size) (cons (hash-chunk (take data chunk-size)) result))))))

(define (next-largest-power-of-2 v)
  (expt 2 (inexact->exact (ceiling (log2 v)))))

(define (hash data chunk-size)
  (let loop ((data data))
    (if (< (length data) (* 2 chunk-size)) ;2 * chunk size avoids infinite loop due to padding
      data
      (loop (hash-round data chunk-size)))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Matrix stuff

(define (matrix-concat a b)
  (let ((cols-a (matrix->cols a))
	(cols-b (matrix->cols b)))
    (if (not (= (matrix-rows a)
		(matrix-rows b)))
      (error "matrix-concat: matrices have different numbers of rows."))
    (cols->matrix (append cols-a cols-b))))

(define (identity-matrix n)
  (let ((new-matrix (make-new-matrix n n)))
    (do ((i 0 (1+ i)))
      ((= i n) new-matrix)
      (matrix-set! new-matrix i i 1))))

(define (zero-matrix m n)
  (make-new-matrix m n))

(define (zero-matrix? m)
  (let ((cols (matrix->cols m)))
    (fold (lambda (col acc)
	    (if (all-zero? col)
	      acc
	      #f))
	    #t
	    cols)))

(define-record-type <matrix>
		    (*make-matrix rows cols data)
		    matrix?
		    (rows matrix-rows set-matrix-rows!)
		    (cols matrix-columns set-matrix-columns!)
		    (data matrix-data set-matrix-data!))

(set-record-type-printer! <matrix>
			  (lambda (record port)
			    (if (not (= (modulo (vector-length (matrix-data record)) (matrix-columns record)) 0))
			      (error "printing matrix: matrix data array doesn't match dimensions."))
			    (newline)
			    (let ((cols (matrix-columns record)))
			      (let loop ((data (vector->list (matrix-data record))))
			        (if (not (eq? '() data))
			  	  (begin
				      (format #t "| ")
				      (map (lambda (e)
					     (format #t "~a " e))
					   (list-head data cols))
				      (format #t "|\n")
				      (loop (list-tail data cols))))))))




(define (make-new-matrix rows cols)
  (*make-matrix rows cols (make-vector (* rows cols) 0)))

(define (rows->matrix rows)
  (let* ((num-rows (length rows))
	 (new-data (list->vector (apply append rows)))
	 (num-columns (/ (vector-length new-data) num-rows)))
    (*make-matrix num-rows num-columns new-data)))

(define (cols->matrix cols)
  (let ((matt (rows->matrix cols)))
    (matrix-transpose matt)))


(define make-matrix rows->matrix)

(define (matrix-get mat i j)
  (vector-ref (matrix-data mat) (+ j (* i (matrix-columns mat)))))

(define (matrix-set! mat i j val)
  (let ((data (matrix-data mat))
	(rows	(matrix-rows mat))
	(cols	(matrix-columns mat)))
   ; (set-matrix-data! mat
		    (vector-set! data (+ j (* i cols)) val);)
    mat))

(define (matrix-transpose mat)
  (let* ((rows (matrix-rows mat))
	 (cols (matrix-columns mat))
	 (new-matrix (make-new-matrix cols rows)))
    (do ((i 0 (1+ i)))
      ((not (< i rows)))
      (do ((j 0 (1+ j)))
	((not (< j cols)))
	(matrix-set! new-matrix j i (matrix-get mat i j))))
    new-matrix))

(define (matrix->rows mat)
  (let ((cols (matrix-columns mat)))
    (let loop ((data (vector->list (matrix-data mat)))
  	       (rows '()))
      (if (eq? '() data)
	(reverse rows)
	(loop (list-tail data cols) (cons (list-head data cols) rows))))))

(define (matrix->cols mat)
  (matrix->rows (matrix-transpose mat)))

(define (matrix-product a b)
  (let ((rows-a (matrix->rows a))
	(cols-b (matrix->cols b)))
    (rows->matrix
      (map (lambda (col-of-b)
	   (map (lambda (row-of-a)
		  (product col-of-b row-of-a))
		rows-a))
	 cols-b))))

(define list->matrix rows->matrix)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;	stats stuff
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (result-probs bits p)
  (let loop ((error (make-list (length bits) 0))
	     (results '()))
      (let ((result `(,(apply-error error bits) . ,(error-prob error p))))
	    (if (all-one? error)
	      (cons result results)
	      (loop (inc error) (cons result results))))))

(define (compare-results a b)
  (fold (lambda (va res)
	  (let* ((pa (cdr va))
		 (ra (car va))
		 (vb (assoc ra b))
		 (pb (cdr vb))
		 (rb (car vb)))
	    (and (eqv? pa pb) res)))
	#t
	a))

(define (display-results a b)
  (format #t "result A\t prob A\t result B\t prob B \t eqv?\n")
  (format #t "RESULT:\t~a\n"
   (fold (lambda (va res)
	  (let* ((pa (cdr va))
		 (ra (car va))
		 (vb (assoc ra b))
		 (pb (cdr vb))
		 (rb (car vb)))
	    (format #t "~a\t~a\t~a\t~a\t~a\t\n" ra pa rb pb (eqv? pa pb))
	    (and (eqv? pa pb) res)))
	#t
	a)))


(define (compare-probabilities m p disp?)
  (let ((compare-results
	  (if disp?
	    display-results
	    compare-results))
	(ra (result-probs m p))
	(rb (result-probs (invert m) (- 1 p))))
    (compare-results ra rb)))

(define (test-bitstr-of-len n p)
  (let loop ((str (make-list n 0))
	     (res #t))
    (if (all-one? str)
      (and (compare-probabilities str p #t) res)
      (loop (inc str) (and (compare-probabilities str p #t) res)))))









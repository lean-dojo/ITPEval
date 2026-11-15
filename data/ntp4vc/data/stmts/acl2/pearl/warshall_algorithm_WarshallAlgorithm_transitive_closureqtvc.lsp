;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/warshall_algorithm_WarshallAlgorithm_transitive_closureqtvc: the
;; Warshall transitive-closure verification condition over Boolean matrices,
;; including its inductive bounded-path relation and nested loop invariants.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Boolean matrices remain arbitrary objects observed through total row,
;; column, and entry operations.  This predicate supplies the source matrix
;; invariant and Boolean element type without bounding the dimensions.

(defstub warshall-rows (matrix) t)
(defstub warshall-columns (matrix) t)
(defstub warshall-elt (matrix row column) t)

(defun warshall-bool-p (value)
  (or (equal value t)
      (equal value nil)))

(defun-sk warshall-matrix-p (matrix)
  (forall
   (row column)
   (and
    (integerp (warshall-rows matrix))
    (integerp (warshall-columns matrix))
    (<= 0 (warshall-rows matrix))
    (<= 0 (warshall-columns matrix))
    (implies
     (and (integerp row)
          (integerp column))
     (warshall-bool-p
      (warshall-elt matrix row column))))))

(defun warshall-same-dimensions-p (left right)
  (and
   (equal (warshall-rows left)
          (warshall-rows right))
   (equal (warshall-columns left)
          (warshall-columns right))))

(defun warshall-valid-index-p (matrix row column)
  (and
   (integerp row)
   (integerp column)
   (<= 0 row)
   (< row (warshall-rows matrix))
   (<= 0 column)
   (< column (warshall-columns matrix))))

;; A source path derivation is equivalently a finite sequence of at least two
;; integer vertices.  Adjacent vertices are matrix edges, and every internal
;; vertex lies in [0,k).  A direct edge is Path_empty; concatenating the two
;; sequences at an internal vertex is Path_cons, and conversely every such
;; sequence yields a finite constructor derivation.

(defun warshall-integer-list-p (vertices)
  (if (consp vertices)
      (and
       (integerp (car vertices))
       (warshall-integer-list-p (cdr vertices)))
    (equal vertices nil)))

(defun warshall-path-edges-p (matrix vertices)
  (if (consp vertices)
      (if (consp (cdr vertices))
          (and
           (equal
            (warshall-elt
             matrix
             (car vertices)
             (cadr vertices))
            t)
           (warshall-path-edges-p
            matrix
            (cdr vertices)))
        (equal (cdr vertices) nil))
    nil))

(defun warshall-internal-vertices-p (vertices k)
  (if (and
       (consp vertices)
       (consp (cdr vertices))
       (consp (cddr vertices)))
      (and
       (<= 0 (cadr vertices))
       (< (cadr vertices) k)
       (warshall-internal-vertices-p
        (cdr vertices)
        k))
    t))

(defun warshall-path-witness-p
    (vertices matrix source destination k)
  (and
   (warshall-integer-list-p vertices)
   (consp vertices)
   (consp (cdr vertices))
   (equal (car vertices) source)
   (equal (car (last vertices)) destination)
   (warshall-path-edges-p matrix vertices)
   (warshall-internal-vertices-p vertices k)))

(defun-sk warshall-path-p
  (matrix source destination k)
  (exists
   (vertices)
   (and
    (warshall-matrix-p matrix)
    (integerp source)
    (integerp destination)
    (integerp k)
    (warshall-path-witness-p
     vertices matrix source destination k))))

;; These three predicates are the k-loop, i-loop, and j-loop invariants from
;; the exported verification condition.

(defun-sk warshall-k-invariant-p
  (current original n k)
  (forall
   (x y)
   (implies
    (and
     (integerp x)
     (integerp y)
     (<= 0 x)
     (< x n)
     (<= 0 y)
     (< y n))
    (iff
     (equal (warshall-elt current x y) t)
     (warshall-path-p original x y k)))))

(defun-sk warshall-i-invariant-p
  (current original n i k)
  (forall
   (x y)
   (implies
    (and
     (integerp x)
     (integerp y)
     (<= 0 x)
     (< x n)
     (<= 0 y)
     (< y n))
    (iff
     (equal (warshall-elt current x y) t)
     (if (< x i)
         (warshall-path-p original x y (+ k 1))
       (warshall-path-p original x y k))))))

(defun-sk warshall-j-invariant-p
  (current original n i j k)
  (forall
   (x y)
   (implies
    (and
     (integerp x)
     (integerp y)
     (<= 0 x)
     (< x n)
     (<= 0 y)
     (< y n))
    (iff
     (equal (warshall-elt current x y) t)
     (if (or
          (< x i)
          (and
           (equal x i)
           (< y j)))
         (warshall-path-p original x y (+ k 1))
       (warshall-path-p original x y k))))))

;; Matrix copying and the nested Function.update equality are retained
;; extensionally over every mathematical integer index.

(defun-sk warshall-copy-p (target source)
  (forall
   (row column)
   (implies
    (and
     (integerp row)
     (integerp column)
     (<= 0 row)
     (< row (warshall-rows target))
     (<= 0 column)
     (< column (warshall-columns target)))
    (equal
     (warshall-elt target row column)
     (warshall-elt source row column)))))

(defun-sk warshall-update-p
  (after before updated-row updated-column value)
  (forall
   (row column)
   (implies
    (and
     (integerp row)
     (integerp column))
    (equal
     (warshall-elt after row column)
     (if (and
          (equal row updated-row)
          (equal column updated-column))
         value
       (warshall-elt before row column))))))

(defun-sk warshall-all-t4-p
  (t3 original n i j k value)
  (forall
   (t4)
   (implies
    (and
     (warshall-matrix-p t4)
     (warshall-same-dimensions-p t4 t3))
    (implies
     (warshall-update-p t4 t3 i j value)
     (warshall-j-invariant-p
      t4 original n i (+ j 1) k)))))

(defun-sk warshall-all-values-p
  (t3 original n i j k old-value)
  (forall
   (value)
   (implies
    (warshall-bool-p value)
    (implies
     (if (equal old-value t)
         (equal value t)
       (if (equal (warshall-elt t3 i k) t)
           (equal value (warshall-elt t3 k j))
         (equal value nil)))
     (and
      (warshall-valid-index-p t3 i j)
      (warshall-all-t4-p
       t3 original n i j k value))))))

(defun warshall-j-body-p
    (t3 original n i j k)
  (and
   (warshall-valid-index-p t3 i j)
   (let ((old-value (warshall-elt t3 i j)))
     (and
      (implies
       (not (equal old-value t))
       (and
        (warshall-valid-index-p t3 i k)
        (implies
         (equal (warshall-elt t3 i k) t)
         (warshall-valid-index-p t3 k j))))
      (warshall-all-values-p
       t3 original n i j k old-value)))))

(defun-sk warshall-all-j-p
  (t3 original n i k o3)
  (forall
   (j)
   (implies
    (integerp j)
    (implies
     (and
      (<= 0 j)
      (<= j o3)
      (warshall-j-invariant-p
       t3 original n i j k))
     (warshall-j-body-p
      t3 original n i j k)))))

(defun warshall-t3-obligations-p
    (t3 original n i k o3)
  (and
   (warshall-all-j-p t3 original n i k o3)
   (implies
    (warshall-j-invariant-p
     t3 original n i (+ o3 1) k)
    (warshall-i-invariant-p
     t3 original n (+ i 1) k))))

(defun-sk warshall-all-t3-p
  (t2 original n i k o3)
  (forall
   (t3)
   (implies
    (and
     (warshall-matrix-p t3)
     (warshall-same-dimensions-p t3 t2))
    (warshall-t3-obligations-p
     t3 original n i k o3))))

(defun warshall-i-body-p
    (t2 original n i k)
  (let ((o3 (- n 1)))
    (and
     (implies
      (<= 0 (+ o3 1))
      (and
       (warshall-j-invariant-p
        t2 original n i 0 k)
       (warshall-all-t3-p
        t2 original n i k o3)))
     (implies
      (< (+ o3 1) 0)
      (warshall-i-invariant-p
       t2 original n (+ i 1) k)))))

(defun-sk warshall-all-i-p
  (t2 original n k o2)
  (forall
   (i)
   (implies
    (integerp i)
    (implies
     (and
      (<= 0 i)
      (<= i o2)
      (warshall-i-invariant-p
       t2 original n i k))
     (warshall-i-body-p
      t2 original n i k)))))

(defun warshall-t2-obligations-p
    (t2 original n k o2)
  (and
   (warshall-all-i-p t2 original n k o2)
   (implies
    (warshall-i-invariant-p
     t2 original n (+ o2 1) k)
    (warshall-k-invariant-p
     t2 original n (+ k 1)))))

(defun-sk warshall-all-t2-p
  (t1 original n k o2)
  (forall
   (t2)
   (implies
    (and
     (warshall-matrix-p t2)
     (warshall-same-dimensions-p t2 t1))
    (warshall-t2-obligations-p
     t2 original n k o2))))

(defun warshall-k-body-p
    (t1 original n k)
  (let ((o2 (- n 1)))
    (and
     (implies
      (<= 0 (+ o2 1))
      (and
       (warshall-i-invariant-p
        t1 original n 0 k)
       (warshall-all-t2-p
        t1 original n k o2)))
     (implies
      (< (+ o2 1) 0)
      (warshall-k-invariant-p
       t1 original n (+ k 1))))))

(defun-sk warshall-all-k-p
  (t1 original n o1)
  (forall
   (k)
   (implies
    (integerp k)
    (implies
     (and
      (<= 0 k)
      (<= k o1)
      (warshall-k-invariant-p
       t1 original n k))
     (warshall-k-body-p
      t1 original n k)))))

(defun warshall-t1-obligations-p
    (t1 original n o1)
  (and
   (warshall-all-k-p t1 original n o1)
   (implies
    (warshall-k-invariant-p
     t1 original n (+ o1 1))
    (warshall-k-invariant-p
     t1 original n (warshall-rows original)))))

(defun-sk warshall-all-t1-p
  (initial original n o1)
  (forall
   (t1)
   (implies
    (and
     (warshall-matrix-p t1)
     (warshall-same-dimensions-p t1 initial))
    (warshall-t1-obligations-p
     t1 original n o1))))

(defun
    ntp4vc-pearl-warshall-algorithm-warshallalgorithm-transitive-closureqtvc-statement
    (m initial)
  (implies
   (and
    (warshall-matrix-p m)
    (warshall-matrix-p initial)
    (equal (warshall-rows m)
           (warshall-columns m))
    (equal (warshall-rows initial)
           (warshall-rows m))
    (equal (warshall-columns initial)
           (warshall-columns m))
    (warshall-copy-p initial m))
   (let ((n (warshall-rows m))
         (o1 (- (warshall-rows m) 1)))
     (and
      (implies
       (<= 0 (+ o1 1))
       (and
        (warshall-k-invariant-p initial m n 0)
        (warshall-all-t1-p initial m n o1)))
      (implies
       (< (+ o1 1) 0)
       (warshall-k-invariant-p
        initial m n (warshall-rows m)))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q

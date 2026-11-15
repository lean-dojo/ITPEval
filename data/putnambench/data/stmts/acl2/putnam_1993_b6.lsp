;; Statement-only formalization of PutnamBench corpus artifact putnam_1993_b6:
;; every positive triple of natural numbers can reach a triple containing zero
;; by finitely many allowed doubling-and-subtraction moves. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A state is the exact Fin 3 -> Nat object from the source, represented by
;; its three values. For distinct indices, the source hypothesis on F uniquely
;; determines F I J STATE: if STATE[I] <= STATE[J], double the former entry and
;; subtract it from the latter; otherwise leave the state unchanged. Since the
;; conclusion only uses distinct indices, eliminating F in favor of this
;; canonical operation is bidirectionally equivalent to the source statement.

(defun putnam-1993-b6-state-p (triple)
  (and
   (true-listp triple)
   (equal (len triple) 3)
   (natp (nth 0 triple))
   (natp (nth 1 triple))
   (natp (nth 2 triple))))

(defun putnam-1993-b6-zero-state-p (triple)
  (or
   (equal (nth 0 triple) 0)
   (equal (nth 1 triple) 0)
   (equal (nth 2 triple) 0)))

(defun putnam-1993-b6-step (triple i j)
  (if
      (and
       (putnam-1993-b6-state-p triple)
       (natp i)
       (< i 3)
       (natp j)
       (< j 3)
       (not (equal i j))
       (<= (nth i triple) (nth j triple)))
      (update-nth
       j
       (- (nth j triple) (nth i triple))
       (update-nth i (* 2 (nth i triple)) triple))
    triple))

;; This recursion is the internal existential quantifier over all finite
;; sequences of ordered, distinct index pairs. It is true exactly when some
;; allowed path of length at most FUEL reaches a zero state.

(defun putnam-1993-b6-reachable-p (triple fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (putnam-1993-b6-zero-state-p triple)
      t
    (if (zp fuel)
        nil
      (let ((next-fuel (- fuel 1)))
        (or
         (putnam-1993-b6-reachable-p
          (putnam-1993-b6-step triple 0 1) next-fuel)
         (putnam-1993-b6-reachable-p
          (putnam-1993-b6-step triple 0 2) next-fuel)
         (putnam-1993-b6-reachable-p
          (putnam-1993-b6-step triple 1 0) next-fuel)
         (putnam-1993-b6-reachable-p
          (putnam-1993-b6-step triple 1 2) next-fuel)
         (putnam-1993-b6-reachable-p
          (putnam-1993-b6-step triple 2 0) next-fuel)
         (putnam-1993-b6-reachable-p
          (putnam-1993-b6-step triple 2 1) next-fuel))))))

;; Every move preserves the natural-valued state and its sum. For initial sum
;; TOTAL, every reachable coordinate is at most TOTAL, so there are at most
;; (TOTAL+1)^3 reachable candidate states. Any path to zero can have loops
;; removed, making this finite bound exactly equivalent to the source's
;; unbounded existential quantification over N and the trajectory Ss.

(defun putnam-1993-b6-path-bound (triple)
  (expt
   (+ 1
      (nth 0 triple)
      (nth 1 triple)
      (nth 2 triple))
   3))

(defun putnambench-putnam-1993-b6-statement (s0 s1 s2)
  (implies
   (and
    (posp s0)
    (posp s1)
    (posp s2))
   (let ((initial-state (list s0 s1 s2)))
     (putnam-1993-b6-reachable-p
      initial-state
      (putnam-1993-b6-path-bound initial-state)))))

(value-triple :itpeval-statement-checked)
:q

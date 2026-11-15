;; Statement-only formalization of VERINA corpus artifact verina_advanced_8,
;; catalog title canCompleteCircuit: the executable gas-station circuit
;; algorithm, its nonempty equal-length input precondition, and its
;; minimal-valid-start correctness contract. This file contains no proof.

(in-package "ACL2")

(defun va8-integer-listp (xs)
  (if (consp xs)
      (and (integerp (car xs))
           (va8-integer-listp (cdr xs)))
    (equal xs nil)))

(defun va8-can-complete-circuit-precond (gas cost)
  (and (va8-integer-listp gas)
       (va8-integer-listp cost)
       (< 0 (len gas))
       (equal (len gas) (len cost))))

(defun va8-sum-list (xs)
  (if (consp xs)
      (+ (car xs) (va8-sum-list (cdr xs)))
    0))

;; ACL2 cons pairs encode Lean products, so CAR and CDR are respectively the
;; gas and cost components of each element of the zipped list.
(defun va8-zip (gas cost)
  (if (and (consp gas) (consp cost))
      (cons (cons (car gas) (car cost))
            (va8-zip (cdr gas) (cdr cost)))
    nil))

;; This preserves the source's local LOOP helper, including its mismatched-list
;; branch, even though the executable body ultimately calls WALK instead.
(defun va8-loop (g c idx tank start)
  (declare (xargs :measure
                  (+ (acl2-count g) (acl2-count c))))
  (cond ((and (endp g) (endp c))
         start)
        ((and (consp g) (consp c))
         (let ((tank-prime (- (+ tank (car g)) (car c))))
           (if (< tank-prime 0)
               (va8-loop (cdr g) (cdr c)
                         (+ idx 1) 0 (+ idx 1))
             (va8-loop (cdr g) (cdr c)
                       (+ idx 1) tank-prime start))))
        (t -1)))

(defun va8-walk (pairs index tank start)
  (declare (xargs :measure (acl2-count pairs)))
  (if (consp pairs)
      (let* ((pair (car pairs))
             (new-tank (- (+ tank (car pair)) (cdr pair))))
        (if (< new-tank 0)
            (va8-walk (cdr pairs) (+ index 1) 0 (+ index 1))
          (va8-walk (cdr pairs) (+ index 1) new-tank start)))
    start))

(defun va8-can-complete-circuit (gas cost)
  (let ((total-gas (va8-sum-list gas))
        (total-cost (va8-sum-list cost)))
    (if (< total-gas total-cost)
        -1
      (va8-walk (va8-zip gas cost) 0 0 0))))

(defun va8-nth-int-default-zero (xs index)
  (cond ((or (not (natp index)) (endp xs))
         0)
        ((zp index)
         (car xs))
        (t
         (va8-nth-int-default-zero (cdr xs) (- index 1)))))

;; This is the fold over List.range (i + 1) in the source VALID predicate.
(defun va8-prefix-balance-aux
    (gas cost start circuit-length offset remaining balance)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      balance
    (let* ((station (mod (+ start offset) circuit-length))
           (next-balance
            (- (+ balance (va8-nth-int-default-zero gas station))
               (va8-nth-int-default-zero cost station))))
      (va8-prefix-balance-aux
       gas cost start circuit-length (+ offset 1) (- remaining 1)
       next-balance))))

(defun va8-prefix-balance (gas cost start circuit-length steps)
  (va8-prefix-balance-aux
   gas cost start circuit-length 0 steps 0))

;; Iterate over List.range circuit-length.  At index I, recompute the source
;; fold over the first I+1 legs and require its accumulated tank to be
;; nonnegative.
(defun va8-valid-prefixes-p
    (gas cost start circuit-length index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (and (<= 0
             (va8-prefix-balance
              gas cost start circuit-length (+ index 1)))
         (va8-valid-prefixes-p
          gas cost start circuit-length (+ index 1) (- remaining 1)))))

(defun va8-valid-start-p (gas cost start circuit-length)
  (va8-valid-prefixes-p
   gas cost start circuit-length 0 circuit-length))

;; Every natural start in [START, START+REMAINING) fails VALID.
(defun va8-all-starts-invalid-p
    (gas cost circuit-length start remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (and (not (va8-valid-start-p gas cost start circuit-length))
         (va8-all-starts-invalid-p
          gas cost circuit-length (+ start 1) (- remaining 1)))))

(defun va8-int-to-nat (value)
  (if (and (integerp value) (<= 0 value))
      value
    0))

(defun va8-can-complete-circuit-postcond (gas cost result)
  (let ((circuit-length (len gas)))
    (and
     (integerp result)
     (<= -1 result)
     (implies
      (equal result -1)
      (va8-all-starts-invalid-p
       gas cost circuit-length 0 circuit-length))
     (implies
      (<= 0 result)
      (and
       (< result circuit-length)
       (va8-valid-start-p
        gas cost (va8-int-to-nat result) circuit-length)
       (va8-all-starts-invalid-p
        gas cost circuit-length 0 (va8-int-to-nat result)))))))

;; The source postcondition's proof argument is unused, so proof erasure leaves
;; this universally quantified implication with the implementation result
;; explicitly connected to the same postcondition.
(defun-sk verina-advanced-8-can-complete-circuit-spec-satisfied-statement ()
  (forall (gas cost)
    (implies
     (va8-can-complete-circuit-precond gas cost)
     (va8-can-complete-circuit-postcond
      gas cost (va8-can-complete-circuit gas cost)))))

(value-triple :itpeval-statement-checked)
:q

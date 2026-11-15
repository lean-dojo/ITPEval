;; Statement-only formalization of thousand-theorems corpus artifact
;; thousand-theorems__acl2__Q1188392, "Zeckendorf's theorem": greedy
;; Fibonacci-index expansion is an equivalence between natural numbers and
;; finite decreasing lists of indices at least 2 whose adjacent entries differ
;; by at least 2. This file contains no proof.

(in-package "ACL2")

(defun q1188392-fib-pair (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (cons 0 1)
    (let ((previous (q1188392-fib-pair (- n 1))))
      (cons (cdr previous)
            (+ (car previous) (cdr previous))))))

(defun q1188392-fib (n)
  (if (natp n)
      (car (q1188392-fib-pair n))
    0))

(defun q1188392-sum-fib (indices)
  (if (consp indices)
      (+ (q1188392-fib (car indices))
         (q1188392-sum-fib (cdr indices)))
    0))

(defun q1188392-representation-chain-p (indices)
  (if (endp indices)
      t
    (and (natp (car indices))
         (<= 2 (car indices))
         (or (endp (cdr indices))
             (and (<= (+ (cadr indices) 2)
                      (car indices))
                  (q1188392-representation-chain-p
                   (cdr indices)))))))

(defun q1188392-representation-p (indices)
  (and (true-listp indices)
       (q1188392-representation-chain-p indices)))

(defun q1188392-greedy-from-index (remaining index)
  (declare (xargs :measure (nfix index)))
  (if (or (not (natp remaining))
          (zp index))
      nil
    (let ((fib-at-index (q1188392-fib index)))
      (if (<= fib-at-index remaining)
          (cons index
                (q1188392-greedy-from-index
                 (- remaining fib-at-index)
                 (if (<= index 2)
                     0
                   (- index 2))))
        (q1188392-greedy-from-index remaining (- index 1))))))

(defun q1188392-zeckendorf (n)
  (if (natp n)
      (q1188392-greedy-from-index n (+ n 1))
    nil))

(defun-sk thousand-theorems-q1188392-zeckendorf-equivalence-statement ()
  (forall (n indices)
    (and
     (implies
      (natp n)
      (let ((representation (q1188392-zeckendorf n)))
        (and
         (q1188392-representation-p representation)
         (equal (q1188392-sum-fib representation) n))))
     (implies
      (q1188392-representation-p indices)
      (equal
       (q1188392-zeckendorf (q1188392-sum-fib indices))
       indices)))))

(value-triple :itpeval-statement-checked)
:q

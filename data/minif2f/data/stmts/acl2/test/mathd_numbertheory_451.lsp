;; Statement-only formalization of miniF2F corpus artifact
;; mathd_numbertheory_451: the finite set of natural numbers from 2010
;; through 2019 that are sums of the positive divisors of some natural number
;; having exactly four positive divisors has element sum 2016. This file
;; contains no proof.

(in-package "ACL2")

(defun mathd-numbertheory-451-divisor-count-through (m d)
  (declare (xargs :measure (nfix d)))
  (if (zp d)
      0
    (+ (if (equal (mod m d) 0) 1 0)
       (mathd-numbertheory-451-divisor-count-through
        m
        (- d 1)))))

(defun mathd-numbertheory-451-divisor-sum-through (m d)
  (declare (xargs :measure (nfix d)))
  (if (zp d)
      0
    (+ (if (equal (mod m d) 0) d 0)
       (mathd-numbertheory-451-divisor-sum-through
        m
        (- d 1)))))

(defun mathd-numbertheory-451-witness-through-p (n m)
  (declare (xargs :measure (nfix m)))
  (if (zp m)
      nil
    (or
     (and
      (equal
       (mathd-numbertheory-451-divisor-count-through m m)
       4)
      (equal
       (mathd-numbertheory-451-divisor-sum-through m m)
       n))
     (mathd-numbertheory-451-witness-through-p
      n
      (- m 1)))))

(defun mathd-numbertheory-451-member-condition-p (n)
  (and (natp n)
       (<= 2010 n)
       (<= n 2019)
       (mathd-numbertheory-451-witness-through-p n n)))

(defun mathd-numbertheory-451-natural-listp (values)
  (if (consp values)
      (and (natp (car values))
           (mathd-numbertheory-451-natural-listp (cdr values)))
    (equal values nil)))

(defun mathd-numbertheory-451-all-members-valid-p (values)
  (if (consp values)
      (and
       (mathd-numbertheory-451-member-condition-p (car values))
       (mathd-numbertheory-451-all-members-valid-p (cdr values)))
    (equal values nil)))

(defun mathd-numbertheory-451-required-members-present-p
  (candidates values)
  (if (consp candidates)
      (and
       (or
        (not
         (mathd-numbertheory-451-member-condition-p
          (car candidates)))
        (member-equal (car candidates) values))
       (mathd-numbertheory-451-required-members-present-p
        (cdr candidates)
        values))
    (equal candidates nil)))

(defun mathd-numbertheory-451-sum (values)
  (if (consp values)
      (+ (car values)
         (mathd-numbertheory-451-sum (cdr values)))
    0))

(defun mathd-numbertheory-451-statement (s)
  (implies
   (and
    (mathd-numbertheory-451-natural-listp s)
    (no-duplicatesp-equal s)
    (mathd-numbertheory-451-all-members-valid-p s)
    (mathd-numbertheory-451-required-members-present-p
     (list 2010 2011 2012 2013 2014
           2015 2016 2017 2018 2019)
     s))
   (equal (mathd-numbertheory-451-sum s)
          2016)))

(value-triple :itpeval-statement-checked)
:q

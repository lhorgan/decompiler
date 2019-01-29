; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%") (value :invisible))
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%") (value :invisible))
(include-book "acl2s/base-theory" :dir :system :ttags :all)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "custom" :dir :acl2s-modes :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
#|(defun tau-listp (tl)
  (cond ((integerp tl) T)
        ((equal tl nil) T)
        ((true-listp tl) (and (tau-listp (first tl)) (tau-listp (rest tl))))
        )
  )|#

#|(defmacro tau-listp (tl)
  (list 'cond (list (list 'integerp tl) T)
              (list (list 'endp tl) T)
              (list (list 'listp tl) (list 'and (list 'tau-listp (list 'first tl)) (list 'tau-listp (list 'rest tl))))))|#

#|(skip-proofs
(defunc tau-listp2 (tl)
  :input-contract (or (integerp tl) (true-listp tl))
  :output-contract (booleanp (tau-listp2 tl))
  (cond ((integerp tl) T)
        ((equal tl nil) T)
        ((true-listp tl) (and (tau-listp2 (first tl)) (tau-listp2 (rest tl))))
        )
  )
)|#

;(skip-proofs
(defunc tau-listp (tl)
  :input-contract T
  :output-contract (booleanp (tau-listp tl))
  (cond ((integerp tl) T)
        ((equal tl nil) T)
        ((true-listp tl) (and (tau-listp (first tl)) (tau-listp (rest tl))))
        (T nil)
        )
  )
;)

(defthm typing
  (implies (tau-listp x) (or (true-listp x) (integerp x)))
  )

(defmacro lenp (delta n)
  (list 'and (list 'natp n) (list 'true-listp delta) (list '>= (list 'len delta) n))
  )

(defunc i_return (delta)
   :input-contract (and (true-listp delta) (tau-listp delta) (integerp (first delta)))
   :output-contract (integerp (first delta))
   (first delta)
   )

#|(defunc taup (a)
  :input-contract a
  :output-contract (booleanp (taup a))
  (or (natp a) (listp a))
  )|#


(defunc i_dup (delta)
  :input-contract (and (tau-listp delta) (true-listp delta))
  :output-contract (tau-listp (i_dup delta))
  (cons (first delta) delta)
  )

(defunc i_const (n delta)
  :input-contract (and (tau-listp delta) (true-listp delta) (tau-listp n))
  :output-contract (tau-listp (i_const n delta))
  (cons n delta)
  )

(defmacro if_zero (delta a f1 f2)
  (list 'cons (list 'if (list 'equal a 0) f1 f2) delta)
  )


(defmacro goto (delta f)
  (list f delta)
  )

(defunc i_pop (delta)
  :input-contract (and (true-listp delta) (tau-listp delta) (lenp delta 1))
  :output-contract (and (true-listp (i_pop delta)) (tau-listp delta))
  (rest delta)
  )

(defunc i_add (delta)
  :input-contract (and (lenp delta 2) (tau-listp delta) (integerp (first delta)) (integerp (second delta)))
  :output-contract (and (true-listp (i_add delta)) (integerp (first (i_add delta))))
  (cons (+ (first delta) (second delta)) (i_pop (i_pop delta)))
  )

(defunc i_swap (delta)
  :input-contract (and (tau-listp delta) (lenp delta 2))
  :output-contract (and (tau-listp (i_swap delta)) (true-listp delta))
  (cons (second delta) (cons (first delta) (rest (rest delta))))
  )

(defthm nil-if-pop-twice-from-list-of-two
  (implies (and (true-listp x) (tau-listp x) (equal (len x) 2)) (equal (i_pop (i_pop x)) nil))
  )

(defunc i_mul (delta)
  :input-contract (and 
                   (true-listp delta) 
                   (tau-listp delta)
                   (lenp delta 2) 
                   (integerp (first delta)) 
                   (integerp (second delta))
                   )
  :output-contract (and
                    (true-listp (i_mul delta))
                    (tau-listp (i_mul delta))
                    (integerp (first (i_mul delta))))
  :function-contract-hints (nil-if-pop-twice-from-list-of-two)
  (cons (* (first delta) (second delta)) (i_pop (i_pop delta)))
  )

(defunc i_div (delta)
  :input-contract (and 
                   (true-listp delta)
                   (tau-listp delta)
                   (lenp delta 2) 
                   (integerp (first delta)) 
                   (integerp (second delta))
                   (/= (second delta) 0)
                   )
  :output-contract (and
                    (true-listp (i_div delta))
                    (tau-listp (i_div delta))
                    (integerp (first (i_div delta))))
  (cons (floor (/ (first delta) (second delta)) 1) (i_pop (i_pop delta)))
  )

(defunc i_mod (delta)
  :input-contract (and 
                   (true-listp delta)
                   (tau-listp delta)
                   (lenp delta 2) 
                   (integerp (first delta)) 
                   (integerp (second delta))
                   (/= (second delta) 0)
                   )
  :output-contract (and
                    (true-listp (i_mod delta))
                    (tau-listp (i_mod delta))
                    (integerp (first (i_mod delta))))
  (cons (mod (first delta) (second delta)) (i_pop (i_pop delta)))
  )

(defunc is_a_list (list)
  :input-contract (true-listp list)
  :output-contract (booleanp (is_a_list list))
  (cond ((equal list nil) T)
        ((and (true-listp (first list)) #|(atom-listp (first list))|# (equal (len (first list)) 2) (is_a_list (rest list))) T)
        (T nil))
  )

(defunc i_store (delta mu)
  :input-contract (and
                   (true-listp delta)
                   (lenp delta 2)
                   (tau-listp delta)
                   (integerp (first delta))
                   (true-listp mu)
                   (is_a_list mu)
                   )
  :output-contract (and
                    ;(equal (first delta) (first (first (second (i_store delta mu)))))
                    ;(equal (second delta) (second (first (second (i_store delta mu)))))
                    ;(equal (len (first (i_store delta mu))) (- (len delta) 2))
                    (is_a_list (second (i_store delta mu)))
                    (tau-listp (first (i_store delta mu)))
                    )
  (list (i_pop (i_pop delta)) 
        (cons (list (first delta) (second delta)) mu))
  )
  
(defunc get_val (mu key)
  :input-contract (and (true-listp mu)  (is_a_list mu) (integerp key))
  :output-contract (atom key)
  (cond ((equal mu nil) nil)
        ((equal (first (first mu)) key) (second (first mu)))
        (T (get_val (rest mu) key))
        )
  )

(defunc i_load (delta mu)
  :input-contract (and
                   (lenp mu 1)
                   (true-listp mu)
                   (is_a_list mu)
                   (true-listp delta)
                   (tau-listp delta)
                   (lenp delta 1)
                   (integerp (first delta))
                   )
  :output-contract (true-listp (i_load delta mu))
  (let ((val (get_val mu (first delta))))
  (append (if (true-listp val) val (list val)) (i_pop delta)))
  )

(defunc i_lt (delta)
  :input-contract (and (true-listp delta) (lenp delta 2) (tau-listp delta) (integerp (first delta)) (integerp (second delta)))
  :output-contract (and (tau-listp (i_lt delta)) (or (equal (first (i_lt delta)) 1) (equal (first (i_lt delta)) 0)))
  (cons (if (< (first delta) (second delta)) 1 0) (i_pop (i_pop delta)))
  )

(defunc i_gt (delta)
  :input-contract (and (true-listp delta) (lenp delta 2) (tau-listp delta) (integerp (first delta)) (integerp (second delta)))
  :output-contract (and (tau-listp (i_lt delta)) (or (equal (first (i_lt delta)) 1) (equal (first (i_lt delta)) 0)))
  (cons (if (> (first delta) (second delta)) 1 0) (i_pop (i_pop delta)))
  )

(defunc i_equal (delta)
  :input-contract (and (true-listp delta) (lenp delta 2) (tau-listp delta) (integerp (first delta)) (integerp (second delta)))
  :output-contract (and (tau-listp (i_lt delta)) (or (equal (first (i_lt delta)) 1) (equal (first (i_lt delta)) 0)))
  (cons (if (equal (first delta) (second delta)) 1 0) (i_pop (i_pop delta)))
  )

(defunc tau-boolp (num)
  :input-contract (integerp num)
  :output-contract (booleanp (tau-boolp num))
  (or (= num 1) (= num 0))
  )

#| we don't need BYTES in the BODY of the function
but ACL2 complains if we don't have it, so we
cons it and then ignore it |#
(defunc i_push (bytes val delta)
  :input-contract (and (integerp val)
                       (integerp bytes)
                       (>= bytes 1) 
                       (<= bytes 32) 
                       (>= val 0) 
                       (< val (expt 2 bytes))
                       (true-listp delta)
                       (tau-listp delta))
  :output-contract (tau-listp (i_push bytes val delta))
  #|(declare (ignore bytes))|#
  (cons val (rest (cons bytes delta)))
  )

(defunc fetch (delta ind)
  :input-contract (and (integerp ind)
                       (>= ind 1)
                       (<= ind 16)
                       (true-listp delta)
                       (tau-listp delta)
                       (lenp delta ind))
  :output-contract (tau-listp (fetch delta ind))
  (if (equal ind 1) (first delta) (fetch (rest delta) (- ind 1)))
  )

(defunc i_dup_* (ind delta)
  :input-contract (and (true-listp delta)
                       (tau-listp delta)
                       (integerp ind)
                       (>= ind 1)
                       (<= ind 16)
                       (lenp delta ind))
  :output-contract (tau-listp (i_dup_* ind delta))
  (cons (fetch delta ind) delta)
  )

(defthm rest_tau
  (implies (and (true-listp delta)
                (tau-listp x)
                (>= (len x) 1))
           (tau-listp (rest x)))
  )

(defthm grk
  (implies (and (true-listp x) (>= (len x) 1)) (true-listp (rest x)))
  )

#|(skip-proofs|#
#|(defunc i_set_* (delta ind val)
  :input-contract (and (tau-listp val)
                       (integerp ind)
                       (>= ind 1)
                       (<= ind 16)
                       (true-listp delta)
                       (tau-listp delta)
                       (lenp delta ind))
  :output-contract (tau-listp (i_set_* delta ind val))
  :body-contracts-hints (("Goal"
           :do-not-induct nil))
  (if (equal ind 1)
    (cons val (rest delta))
    (cons (first delta) (i_set_* (rest delta) (- ind 1) val))
  ))|#
#|)|#

(defthm duh
  (implies (and (true-listp x)
                (tau-listp (first x))
                (tau-listp (rest x))
                )
           (tau-listp x)))

(defthm duh2
  (implies (and (true-listp x)
                (tau-listp x)
                (posp ind)
                (>= (len x) ind)
                )
           (equal (set-difference$ (subseq x 0 (- ind 1)) x) nil)
           )
  )

#|(defthm duh3
  (implies (and (true-listp x)
                (tau-listp x)
                (posp ind)
                (>= (len x) ind)
                )
           (implies (set-difference$ (subseq x 0 (- ind 1)) x)
                    (tau-listp (nth (- ind 1) x))
                    )
  )
  )|#

#|(defthm duh3
  (implies (and (true-listp x)
                (tau-listp x)
                (posp ind)
                (>= (len x) ind)
                )
           (tau-listp (nth (- ind 1) x))
  )
  )|#

#|(defthm grk2
  (implies (and (true-listp x)
               (tau-listp x)
               (posp i)
               (>= (len x) i))     
          (tau-listp (subseq x 0 i))
  ))|#

(defthm erg
  (implies (and (true-listp x)
                (tau-listp x)
                (tau-listp y)
                )
           (tau-listp (cons y x))))

(defthm erg2
  (implies (and (true-listp x)
                (tau-listp x)
                )
           (tau-listp (rest x))))

(defthm grk3
  (implies (and (true-listp x)
                (consp x)
                (tau-listp x)
                )
           (tau-listp (rest x))))

(defunc i_remove_first (delta n)
  :input-contract (and (true-listp delta)
                       (tau-listp delta)
                       (natp n)
                       (<= n (len delta)))
  :output-contract (tau-listp (i_remove_first delta n))
  (cond ((= n 0) delta)
        (T (i_remove_first (rest delta) (- n 1))))
        
  )

(defthm nth-tau-list-induct
  (implies (and (true-listp x)
                (tau-listp x)
                (natp n)
                (= n 0))
           (= (first x) (nth n x))
  )
  )

(defthm nth-tau-list-induct2
  (implies (and (true-listp x)
                (tau-listp x))
           (tau-listp (rest x))))#|ACL2s-ToDo-Line|#

#|defunc blah (delta1 delta2 n)
  :input-contract (and (true-listp delta1)
                       (true-listp delta2)
                       (tau-listp delta1)
                       (tau-listp delta2)
                       (natp n)
                       )
  :output-contract 
  (cond ((= n (len delta1)) (and (tau-listp (first delta2)) (tau-listp (nth n delta1))))
        (T (and (tau-listp (first delta2)) (tau-listp (nth n delta1)) (blah delta1 (rest delta2) (+ n 1))))
        )
  )|#

#|(defunc messy-swap (delta n)
  :input-contract (and (true-listp delta)
                       (tau-listp delta)
                       (natp n)
                       (<= n (len delta)))
  (cons
  )

(defunc yippy (x)
  :input-contract
  :output-contract
  (let ((n (
  )|#



(defunc grk7 (a)
  :input-contract (and T
                       (tau-listp a))
  :output-contract (tau-listp (grk7 a))
  (cond ((equal a nil) a)
        ((integerp a) a)
        ((true-listp a) (cons (first a) (grk7 (rest a))))
        (T nil)
        )
  )

;(skip-proofs
(defunc messy-swap (delta #|n curr val)|#)
  :input-contract (and (true-listp delta)
                       (tau-listp delta)
                       ;(tau-listp val)
                       ;(posp n)
                       ;(posp curr)
                       ;(<= n (len delta))
                       #|(<= curr n)|#
                       )
  :output-contract (tau-listp (messy-swap delta #|n curr val|#))
  (cond ;((equal curr n) (cons (first delta) (messy-swap (rest delta) n (+ curr 1) val)))
        ((equal delta nil) nil)
        (T (cons (first delta) (messy-swap (rest delta) #|n (+ curr 1) val))))|#))))
         
  )
;)

(defaxiom tau-list-fun
  (implies (and (true-listp x)
                (tau-listp x)
                (natp n)
                (< n (len x)))
           (tau-listp (nth n x)))
  )

(defthm nth-tau-list-induct3
  (implies (and (true-listp x)
                (tau-listp x)
                (= n 0))
           (blah x x n)))
           
(defthm nth-tau-list-induct4
  (implies (and (true-listp x)
                (tau-listp x)
                (natp n)
                (= n 2)
           (tau-listp (nth (- n 1) x))))
           

(defthm grk4
  (implies (and (true-listp x)
                (tau-listp x)
                )
           (tau-listp (reverse x))))

(defunc i_remove_last (delta)
  :input-contract (and (true-listp delta)
                       (tau-listp delta)
                       #|(natp n)
                       (<= n (len delta))|#)
  :output-contract (tau-listp (i_remove_last delta))
  (reverse delta)
  )


#|(defunc i_remove_first (delta n)
  :input-contract (and (true-listp delta)
                       (tau-listp delta)
                       (posp n)
                       (<= n (len delta)))
  :output-contract (tau-listp (i_remove first delta n))
  (i_remove_last (reverse delta) n)
  )

(defunc i_subseq (delta end curr)
  :input-contract (and (true-listp delta)
                       (tau-listp delta)
                       (natp end)
                       (natp curr)
                       (>= end 1)
                       (<= end 16)
                       (>= curr 1)
                       (<= curr 16)
                       (lenp delta end)
                       )
  :output-contract (tau-listp (i_subseq delta end curr))
  (if (> curr end) nil (cons (fetch delta curr) (i_subseq delta end (+ curr 1))))
  )

(defthm erg3
  (and (true-listp x)
                (tau-listp x)
                (tau-listp y)
                )
  
(skip-proofs
(defunc i_insert_* (delta val ind)
  :input-contract (and (true-listp delta)
                       (tau-listp delta)
                       (tau-listp val)
                       (integerp ind)
                       (>= ind 0)
                       (lenp delta ind))
  :output-contract (tau-listp (i_insert_* delta val ind))
  (if (= ind 0)
    (rest delta)
    (cons (first delta) (i_insert_* (rest delta) val (- ind 1)))
    )
  )
)

(defunc i_swap_* (ind delta)
  :input-contract (and (true-listp delta)
                       (tau-listp delta)
                       (integerp ind)
                       (>= ind 1)
                       (<= ind 16)
                       (lenp delta 2)
                       (lenp delta ind))
  :output-contract (true-listp (i_swap_* ind delta))
  #|(cons (nth (- ind 1) delta)
             (rest (cons (cons (subseq delta 0 (- ind 1)) (first delta)) (subseq delta ind (len delta))))
             )|#
  (subseq delta 0 ind)
  )|#

(include-book "std/strings/top" :dir :system)
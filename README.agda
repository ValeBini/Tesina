------------------------------------------------------------------------
-- Codigo relativo a la Tesina de Grado:
-- "Formalización de Mónadas Concurrentes en Agda: 
-- el Caso de la Mónada Delay"
--
-- Autora: Valentina Bini   -   Director: Exequiel Rivas
------------------------------------------------------------------------

module README where 

------------------------------------------------------------------------
-- Capítulo 5
-- Formalización de Mónadas Concurrentes en Agda

-- Sección 5.1: Formalización en Agda: los monoides
import Structures.Monoid 

-- Sección 5.2: Formalización a nivel de funtores y mónadas
-- -- Sección 5.2.1: Formalización de Mónada 
import Structures.Monad

-- -- Sección 5.2.2: Formalización de Funtor Monoidal
import Structures.MonoidalFunctor 

-- Sección 5.3: Formalización de monoides concurrentes
import Structures.ConcurrentMonoid 

-- Sección 5.4: Formalización de mónadas concurrentes
import Structures.ConcurrentMonad 


------------------------------------------------------------------------
-- Capítulo 6
-- El caso de la Mónada Delay 

-- Sección 6.1: Definición del tipo delay con notación musical 
import Delay 

-- Sección 6.2: Prueba de que el tipo delay es una mónada
import Instances.Monad 

-- Sección 6.3: Prueba de que el tipo delay es un funtor monoidal 
import Instances.MonoidalFunctor

-- Sección 6.4: ¿El tipo delay es una mónada concurrente?
import Instances.ConcurrentMonad 

-- Sección 6.5: Reduciendo el problema a los conaturales
import CoNaturalsM 

-- Sección 6.6: Cambio de paradigma: sized types
-- -- Sección 6.6.1: Definición de los conaturales utilizando sized types 
import CoNaturalsS 

-- -- Sección 6.6.2: Prueba de que los conaturales forman un monoide concurrente
import CoNaturalsS
import Instances.ConcurrentMonoid

-- -- Sección 6.6.3: Una mónada concurrente alternativa a delay 
import Proofs.ConcMonoid->ConcMonad
import Instances.AltConcurrentMonad
/* M_Votacao
 * Author: estud
 * Creation date: 20/11/2026
 */
MACHINE
    M_Votacao
    
SEES
    M_VotacaoCtx

VARIABLES
    estado, //estado: o estado atual do sistema de votação;
    eleitores, // os eleitores registrados;
    candidatos, // os candidatos registrados;
    local, //o local de votação de cada eleitor;
    votos, //a quantidade de votos de cada candidato;
    registro // a informação se cada eleitor votou ou não.

INVARIANT
   estado : ESTADO & 
   eleitores : POW(CPF) &
   candidatos : POW(eleitores) & //Todo candidato é também um eleitor.
   local : eleitores --> ZONAS &
   votos: candidatos --> NAT &
   registro : eleitores --> BOOL &
   
   cpf_indef /: eleitores &
   cpf_indef /: candidatos &
   ((estado = preparacao) => ((TRUE /: ran(registro) & (ran(votos) = {0} or votos = {}))))
   
  
INITIALISATION
    estado := preparacao || eleitores := {} || candidatos := {} || local := {} || votos := {} || registro := {}
    
OPERATIONS
    
    adicionar_eleitor(eleitor, zona) =
    
    PRE
        eleitor : CPF &
        estado = preparacao &
        zona : ZONAS &
        eleitor /: eleitores &
        eleitor /= cpf_indef
    
    THEN
      
        local(eleitor) := zona ||
        eleitores := eleitores \/ {eleitor} ||
        registro(eleitor) := FALSE

    END;
    
    
    remover_eleitor(eleitor) =
    
    PRE
        eleitor : eleitores &
        estado = preparacao
        
    THEN
        eleitores := eleitores - {eleitor} ||
        IF eleitor : candidatos THEN candidatos := candidatos - {eleitor} || votos := {eleitor} <<| votos  END ||
        local := {eleitor} <<| local ||
        registro := {eleitor} <<| registro
       // local := local - {(eleitor |-> local(eleitor))} ||
        //registro := registro - {(eleitor |-> registro(eleitor))}
    
    END;
    
    
    mudar_local(eleitor, nova_zona) =
    
    PRE
        estado = preparacao &
        eleitor : eleitores &
        nova_zona : ZONAS &
        nova_zona /= local(eleitor)
    
    
    THEN
        local(eleitor) := nova_zona
    
    END;
    
    
    adicionar_candidato(eleitor) =
    
    PRE
        estado = preparacao &
        eleitor : eleitores
    
    THEN
        IF eleitor : candidatos THEN skip
          
        ELSE candidatos := candidatos \/ {eleitor} || votos(eleitor) := 0
        
        END
    END;
    
    
    remover_candidato(eleitor) =
    
    PRE
        estado = preparacao &
        eleitor : candidatos
    
    THEN
        candidatos := candidatos - {eleitor} || votos := {eleitor} <<| votos
        
    END;
    
    
    inicar_votacao =
    
    PRE
        estado = preparacao &
        card(candidatos) > 0
    THEN
        estado:= votacao
        
    END;
    
    votar(eleitor, zona_atual, candidato) =
    PRE
        eleitor : eleitores &
        zona_atual : ZONAS &
        candidato : CPF &
        estado = votacao &

        zona_atual = local(eleitor) &
        registro(eleitor) = FALSE &

        (candidato : candidatos or candidato = cpf_indef)
        
    THEN
        IF candidato : candidatos THEN votos(candidato) := votos(candidato) + 1 END ||
        registro(eleitor) := TRUE
    
    END;


    concluir_votacao =
    
    PRE
        estado = votacao
        
    THEN
        estado := apuracao
        
    END;
    
    
    resultado <-- apurar_vencedor =
        PRE
            estado = apuracao
        
        THEN
            IF max(ran(votos)) = 0 THEN resultado := cpf_indef
            
            ELSIF card(votos|>{(max(ran(votos)))}) > 1 THEN resultado := cpf_indef
                
            ELSE
                ANY candidato WHERE 
                    candidato : candidatos &
                    votos(candidato) = max(ran(votos))
                THEN
                    IF max(ran(votos)) <= (SIGMA ii . (ii : dom(votos)|votos(ii))) / 2 THEN resultado := cpf_indef
                    ELSE resultado := candidato
                    END
                END
                
            END
                    

        END
      
    

    
END

/*
 * UNIVERSIDADE FEDERAL DE PERNAMBUCO
 * CENTRO DE INFORMATICA
 * CIENCIA DA COMPUTACAO
 *
 * SISTEMAS CRITICOS 2022.1
 * EXERCICIO ESCOLAR (17/10/2022)
 * PROFESSOR: GUSTAVO CARVALHO
 *
 * PONTUACAO
 * 1a questao  =  0,5 ponto
 * 2a questao  =  0,5 ponto 
 * 3a questao  =  1,0 ponto
 * 4a questao  =  1,0 ponto
 * 5a questao  =  0,5 ponto
 * 6a questao  =  1,0 ponto
 * 7a questao  =  1,0 ponto 
 * 8a questao  =  1,0 ponto
 * 9a questao  =  0,5 ponto
 * 10a questao =  0,5 ponto
 * 11a questao =  0,5 ponto
 * 12a questao =  1,0 ponto
 * 13a questao =  1,0 ponto 
 * ------total = 10,0 pontos
 */
 
// ALUNO: Paula Nóbrega de Campos Guimarães

// Especifique formalmente (em B) um sistema de controle de provas de corrida, conforme aas orientacoes a seguir. A priori, nao ha necessidade de adicionar novas variaveis aa maquina. Nao mude a assinatura das operacoes. Sugestao: utilize o ProB para simular (validar) seu modelo, como tambem procurar por violacoes de invariantes.

MACHINE
    MCorridaEnunciado
SETS
 
// 1a questao
// Defina adequadamente os seguintes conjuntos:
// - MODALIDADES: existem quatro modalidades de corrida (CINCO, DEZ, MEIA e MARATONA);
// - STATUS_CORRIDA: existem tres status possiveis (NAO_INICIADA, INICIADA e ENCERRADA);
// - CPF: CPF das pessoas que podem se inscrever na corrida.

    MODALIDADES = {CINCO, DEZ, MEIA, MARATONA};
    STATUS_CORRIDA = {NAO_INICIADA, INICIADA, ENCERRADA};
    CPF

CONSTANTS
    VALOR // Valor da inscricao em cada modalidade.
    
PROPERTIES
    
// 2a questao
// Defina adequadamente o tipo e as informacoes associadas aa constante VALOR.
// VALOR associada um NAT para cada modalidade de corrida.
// A inscricao em uma prova de CINCO km custa 2.
// A inscricao em uma prova de DEZ km custa 2.
// A inscricao em uma MEIA maratona custa 4.
// A inscricao em uma MARATONA custa 6.
    
    VALOR : MODALIDADES --> NAT &
    VALOR(CINCO) = 2 &
    VALOR(DEZ) = 2 &
    VALOR(MEIA) = 4 &
    VALOR(MARATONA) = 6
//    VALOR = {(CINCO |-> 2), (DEZ |-> 2), (MEIA |-> 4), (MARATONA |-> 6)}

VARIABLES
    
    inscricoes, // Associa ao CPF dos participantes inscritos a respectiva modalidade de corrida.
    
    inscricoes_pagas, // Associa um BOOL a cada inscricao, informando se a mesma foi paga ou nao.
    
    inscricoes_confirmadas, // Um subconjunto de inscricoes contendo somente as incricoes confirmadas.
    
    inscricoes_abertas, // Um BOOL indicando se novas inscricoes podem ser feitas.
    
    inscricoes_processadas, // Um BOOL indicando se as inscricoes realizadas foram processadas.
    
    valor_arrecadado, // Um NAT com o valor total arrecadado com as incricoes.
    
    status_corrida, // O status atual da corrida, dentre os status possiveis.
    
    tempo_largada, // Associada um INT a cada participante confirmado, informando o seu tempo de largada.
    
    tempo_chegada // Associada um INT a cada participante, informando o seu tempo de chegada.
    
INVARIANT

// 3a questao
// Defina adequadamente o tipo das variaveis declaradas anteriormente.
    
    
    inscricoes: CPF +-> MODALIDADES &
    inscricoes_pagas : dom(inscricoes) --> BOOL & //LEMBRAR DE PERGUNTAR POR QUE CARALHOS PRECISA DO DOM
    inscricoes_confirmadas <: dom(inscricoes) & 
    inscricoes_abertas : BOOL &
    inscricoes_processadas : BOOL &
    valor_arrecadado : NAT &
    status_corrida : STATUS_CORRIDA &
    tempo_largada : inscricoes_confirmadas --> INT &
    tempo_chegada : inscricoes_confirmadas --> INT &

// 4a questao
// Formalize as duas seguintes invariantes do sistema:
// - Nas variaveis tempo_largada e tempo_chegada, o valor associado a cada participante
// deve ser maior ou igual a -1. O valor -1 sera utilizado para representar que o
// participante em questao ainda nao passou pelo portico de largada ou chegada, respectivamente.
// - Para todo participante confirmado, se o seu tempo de chegada for diferente de -1
// (ou seja, ele passou pelo portico de chegada), o tempo de largada deve ser diferente de -1
// e o tempo de chegada deve ser maior do que o tempo de largada.

    !tempo . ((tempo : INT & tempo : ran(tempo_largada)) => (tempo >= -1)) &
    !tempo . ((tempo : INT & tempo : ran(tempo_largada)) => (tempo >= -1)) &
    !cpf . ((cpf: CPF & cpf : inscricoes_confirmadas & tempo_chegada(cpf) > -1 & tempo_chegada /= {} & tempo_largada /= {}) => (tempo_largada(cpf) > -1 & tempo_chegada(cpf) > tempo_largada(cpf)))

INITIALISATION
    inscricoes := {} // Inicializacao das variaveis do sistema.
    || inscricoes_pagas := {} // Inicializacao das variaveis do sistema.
    || inscricoes_confirmadas := {} // Inicializacao das variaveis do sistema.
    || inscricoes_abertas := FALSE // Inicializacao das variaveis do sistema.
    || inscricoes_processadas := FALSE // Inicializacao das variaveis do sistema.
    || valor_arrecadado := 0 // Inicializacao das variaveis do sistema.
    || status_corrida := NAO_INICIADA // Inicializacao das variaveis do sistema.
    || tempo_largada := {} // Inicializacao das variaveis do sistema.
    || tempo_chegada := {} // Inicializacao das variaveis do sistema.

OPERATIONS
    
// 5a questao
// Defina as seguintes operacoes:
// - abrir_inscricoes: permite que novas inscricoes sejam realizadas. A operacao
// so pode ser realizada se as incricoes estiverem fechadas e as inscricoes
// ainda nao tiverem sido processadas.
// - fechar_inscricoes: fecha as inscricoes. A operacao so pode ser realizada
// se as inscricoes estiverem abertas.

    abrir_inscricoes =
    
        PRE
            inscricoes_abertas = FALSE &
            inscricoes_processadas = FALSE
            
        THEN
            inscricoes_abertas := TRUE
            
        END;
      
      
     fechar_inscricoes =
    
        PRE
            inscricoes_abertas = TRUE
            
        THEN
            inscricoes_abertas := FALSE
            
        END;
        


// 6a questao
// Defina as seguintes operacoes:
// - realizar_inscricao: dado um cpf e uma modalidade de corrida, realiza uma nova
// inscricao. O cpf precisa ser de um participante ainda nao inscrito. Alem disso,
// as inscricoes precisam estar abertas. Ao realizar esta operacao, o pagamento
// da nova inscricao ficara como pendente (associando FALSE em inscricoes_pagas).

// - pagar_inscricao: dado um cpf, esta operacao registra o pagamento da inscricao pendente.
// A operacao so pode ser realizada se as inscricoes ainda nao tiverem sido processadas.
// Ao realizar esta operacao, deve-se atualizar o valor total arrecadado.



    realizar_inscricao(cpf, modalidade) =
    
    PRE
        cpf : CPF &
        cpf /: dom(inscricoes) &
        modalidade : MODALIDADES &
        inscricoes_abertas = TRUE
        
    THEN
        inscricoes(cpf) := modalidade ||
        inscricoes_pagas(cpf) := FALSE
        
    END;
    
    
    pagar_inscricao(cpf) =
    
    PRE
        cpf : dom(inscricoes) &
        inscricoes_pagas(cpf) = FALSE &
        inscricoes_processadas = FALSE
    
    THEN
        inscricoes_pagas(cpf) := TRUE ||
        valor_arrecadado := valor_arrecadado + VALOR(inscricoes(cpf))
        
    END;




// 7a questao
// Defina a a operacao cancelar_inscricao. Dado um cpf de um participante inscrito,
// esta operacao cancela a respectiva inscricao, removendo o participante da lista
// de participantes inscritos. Se o participante ja tiver pago a inscricao,
// devolve-se ao participante somente metade do valor pago. Portanto,
// o valor arrecadado precisa ser atualizado adequadamente.
// Uma inscricao so pode ser cancelada se as inscricoes ainda nao foram processadas.
    
    cancelar_inscricao(cpf) = 
    
    PRE
        cpf : CPF &
        cpf : dom(inscricoes) &
        inscricoes_processadas = FALSE
    
    THEN
        IF inscricoes_pagas(cpf) = TRUE THEN valor_arrecadado := valor_arrecadado - (VALOR(inscricoes(cpf))/2) END ||
        
        inscricoes := {cpf} <<| inscricoes ||
        inscricoes_pagas := {cpf} <<| inscricoes_pagas
        
    END;
        
        
        


// 8a questao
// Defina a operacao processar_inscricoes. Esta operacao so pode ser realizada
// se as inscricoes estiverem fechadas e ainda nao tiverem sido processadas.
// Adicionalmente, deve-se ter pelo menos um participante com inscricao paga.
// Ao realizar esta operacao, sao consideradas confirmadas todas aquelas
// inscricoes que foram pagas. A operacao deve tambem inicializar com o valor -1
// o tempo de largada e chegada dos participantes confirmados.

    processar_inscricoes = 
    
        PRE
            inscricoes_abertas = FALSE &
            inscricoes_processadas = FALSE &
            card(dom(inscricoes_pagas |> {TRUE} )) > 0
            
        THEN
            inscricoes_confirmadas := dom(inscricoes_pagas) ||
            
            tempo_largada := dom(inscricoes_pagas) * {-1} ||
            tempo_chegada := dom(inscricoes_pagas) * {-1} || 
            inscricoes_processadas := TRUE
            
        END;





// 9a questao
// Defina as seguintes operacoes:
// - iniciar_corrida: apos as inscricoes terem sido processadas, considerando tambem
// que a corrida ainda nao foi iniciada, esta operacao muda o status da corrida
// para INICIADA.

    iniciar_corrida =
    
        PRE
            inscricoes_processadas = TRUE &
            status_corrida = NAO_INICIADA
            
        THEN
            
            status_corrida := INICIADA
            
        END;     


// - registrar_tempo_largada: se a corrida ja foi iniciada, esta operacao permite
// registrar o tempo (NAT) em que um dado cpf passou pelo portico de largada. Esse cpf
// precisa ser o de um participante com inscricao confirmada e o seu tempo de largada
// nao deve ter sido registrado (ou seja, ainda deve ser igual a -1).

    registrar_tempo_largada (cpf, tempo) =
    
    PRE
        tempo : NAT &
        cpf : inscricoes_confirmadas &
        status_corrida = INICIADA &
        tempo_largada(cpf) = -1
        
    THEN
        tempo_largada(cpf) := tempo
        
        
    END;
        



// 10a questao
// Defina as seguintes operacoes:
// - registrar_tempo_chegada: se a corrida ja foi iniciada, esta operacao permite
// registrar o tempo (NAT) em que um dado cpf passou pelo portico de chegada. Esse cpf
// preciso ser o de um participante com inscricao confirmada. O tempo de largada
// desse participante ja deve ter sido registrado, mas nao o seu tempo de chegada.
// Por fim, o tempo de chegada deve ser necessariamente maior do que o de largada.


    registrar_tempo_chegada(cpf, tempo) = 
    
    PRE
        tempo : NAT &
        cpf : inscricoes_confirmadas &
        status_corrida = INICIADA &
        tempo_chegada(cpf) = -1 &
        tempo_largada(cpf) /= -1 &
        tempo > tempo_largada(cpf)
        
    THEN
        tempo_chegada(cpf) := tempo
        
    END;



// - encerrar_corrida: se a corrida ja foi iniciada, esta operacao registra o seu termino.

    encerrar_corrida =
    
        PRE
            status_corrida = INICIADA
            
        THEN
            status_corrida := ENCERRADA
            
        END;
            


// 11a questao
// Defina a operacao obter_arrecadacao, que retorna o valor total arrecadado com as inscricoes.

    valor_total <-- obter_arrecadacao =
    
        BEGIN //nada diz que tem que ser depois das inscrições fechadas, então não presumi
            valor_total := valor_arrecadado
            
        END;


// 12a questao
// Definida a operacao obter_total_concluintes que retorna a quantidade de participantes
// que concluiram a corrida. Esta operacao so pode ser realizada apos o termino da corrida.

    concluintes <-- obter_total_concluintes =
    
    PRE
        status_corrida = ENCERRADA
        
    THEN
        concluintes := card(dom(tempo_chegada |>> {-1}))
        
    END;


// 13a questao
// Defina a operacao obter_concluintes_por_modalidade que retorna a quantidade de participantes
// que concluiram a corrida, agrupados por modalidade. Esta operacao so pode ser realizada
// apos o termino da corrida.

    concluintes_cinco, concluintes_dez, concluintes_meia, concluintes_maratona <-- obter_concluintes_por_modalidade =
    
    PRE 
        status_corrida = ENCERRADA
    
    THEN
        concluintes_cinco :=  card((dom(tempo_chegada |>> {-1}) <| inscricoes) |> {CINCO}) ||
        concluintes_dez := card((dom(tempo_chegada |>> {-1}) <| inscricoes) |> {DEZ}) ||
        concluintes_meia := card((dom(tempo_chegada |>> {-1}) <| inscricoes) |> {MEIA}) ||
        concluintes_maratona := card((dom(tempo_chegada |>> {-1}) <| inscricoes) |> {MARATONA})
        
     END

END
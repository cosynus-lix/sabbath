% for size_system = [5]
    load("data_in_common.mat")
    load("data_" + num2str(size_system) + ".mat")
    num_variables = size(GA,1);
    num_outputs = size(GC,1);
    num_controllers = 3;
    reference_values = [0.5, 5, -1, 20]';
    constant_value_invar = Switch_Th - reference_values(1);
    GC1 = GC;
    A_0 = GA;
    B_0 = GB(:,1:3);
    % HERE WE TRY TO SOLVE THE PROBLEM WITH THE -1;
    B_0(:,2) = -B_0(:,2);
    C_0 = GC1;
    KI_0 = KI0;
    KI_1 = KI1;
    KP_1 = KP1;
    KP_0 = KP0;
    A_1 = GA;
    B_1 = GB(:,1:3);
    % HERE WE TRY TO SOLVE THE PROBLEM WITH THE -1;
    B_1(:,2) = -B_1(:,2);
    C_1 = GC1;
    num_modes = 2;
    Invar_0_geq0 = [ GC1(1,:), constant_value_invar];
    Invar_1_geq0 = -[ GC1(1,:), constant_value_invar];
    save("data_to_python/data_to_python_size_"+num2str(size_system)+"_ref" + num2str(reference_values(1)) +" "+ num2str(reference_values(2))+" "+ num2str(reference_values(3))+" "+ num2str(reference_values(4))+".mat" ,"A_0","reference_values","Invar_1_geq0","Invar_0_geq0","num_modes","C_1","B_1","A_1","KP_0","KP_1","KI_1","KI_0","C_0","B_0","num_controllers","num_outputs","num_variables")
    

    A_0_homo_top = [A_0, B_0];
    N_0 = - KP_0 * C_0 * A_0 - KI_0 * C_0;
    M_0 = - KP_0 * C_0 * B_0;
    A_0_homo_bot = [N_0, M_0];
    A_0_homo = [A_0_homo_top; A_0_homo_bot];

    b_0_bot = KI_0 * reference_values;
    b_0_homo = [zeros(num_variables,1); b_0_bot];

    C_0_homo = [C_0, zeros(num_outputs, num_controllers)];

    Invar_0_geq0_homo = [Invar_0_geq0(:,1:num_variables), zeros(size(Invar_0_geq0,1), num_controllers), Invar_0_geq0(:,end) ];

    A_1_homo_top = [A_1, B_1];
    N_1 = - KP_1 * C_1 * A_1 - KI_1 * C_1;
    M_1 = - KP_1 * C_1 * B_1;
    A_1_homo_bot = [N_1, M_1];
    A_1_homo = [A_1_homo_top; A_1_homo_bot];

    b_1_bot = KI_1 * reference_values;
    b_1_homo = [zeros(num_variables,1); b_1_bot];

    C_1_homo = [C_1, zeros(num_outputs, num_controllers)];

    Invar_1_geq0_homo = [Invar_1_geq0(:,1:num_variables), zeros(size(Invar_1_geq0,1), num_controllers), Invar_1_geq0(:,end) ];
    
    A_0_homo_complete = [A_0_homo, b_0_homo; zeros(1, size(A_0_homo,1)) , 0];
    A_1_homo_complete = [A_1_homo, b_1_homo; zeros(1, size(A_1_homo,1)) , 0];
% end